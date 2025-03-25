use super::*;

pub(super) struct FreezableRuneUpdater<'a, 'tx> {
  pub(super) event_sender: Option<&'a mpsc::Sender<Event>>,
  pub(super) lost: HashMap<RuneId, Lot>,
  pub(super) height: u32,
  pub(super) outpoint_to_frozen_rune_id:
    &'a mut MultimapTable<'tx, &'static OutPointValue, RuneIdValue>,
}

pub(super) struct Tables<'a, 'tx> {
  pub id_to_entry: &'a mut Table<'tx, RuneIdValue, RuneEntryValue>,
  pub rune_to_id: &'a Table<'tx, u128, RuneIdValue>,
  pub rune_to_freezable_rune_id: &'a MultimapTable<'tx, u128, RuneIdValue>,
  pub outpoint_id_to_outpoint: &'a Table<'tx, OutPointIdValue, OutPointValue>,
  pub outpoint_to_balances: &'a Table<'tx, &'static OutPointValue, &'static [u8]>,
}

impl<'a, 'tx> FreezableRuneUpdater<'a, 'tx> {
  pub(super) fn pre_process_runes(
    &mut self,
    mut tables: Tables<'_, '_>,
    txid: Txid,
    artifact: &Option<Artifact>,
    unallocated: &mut HashMap<RuneId, Lot>,
    unallocated_by_outpoint: HashMap<OutPoint, Vec<(RuneId, Lot)>>,
  ) -> Result<()> {
    // Mark frozen runes as lost and remove from unallocated
    for (outpoint, balances) in unallocated_by_outpoint {
      let frozen_runes = self
        .outpoint_to_frozen_rune_id
        .remove_all(&outpoint.store())?
        .filter_map(|rune_id| {
          let guard = rune_id.ok()?;
          Some(RuneId::load(guard.value()))
        })
        .collect::<HashSet<RuneId>>();

      for (id, balance) in balances {
        if frozen_runes.contains(&id) {
          // Mark rune as lost if transferred while frozen
          *self.lost.entry(id).or_default() += balance;

          // Remove from unallocated
          *unallocated.entry(id).or_default() -= balance;

          if let Some(sender) = self.event_sender {
            sender.blocking_send(Event::RuneLost {
              block_height: self.height,
              txid,
              rune_id: id,
              amount: balance.0,
              outpoint,
            })?;
          }
        }
      }
    }

    if let Some(Artifact::Runestone(runestone)) = artifact {
      self.freeze(&mut tables, txid, runestone, unallocated)?;

      for (id, found) in self.unfreeze(&mut tables, txid, runestone, unallocated)? {
        *unallocated.entry(id).or_default() += found;
      }
    }

    Ok(())
  }

  pub(super) fn update(
    self,
    id_to_entry: &'a mut Table<'tx, RuneIdValue, RuneEntryValue>,
  ) -> Result {
    for (rune_id, lost) in self.lost {
      let mut entry = RuneEntry::load(id_to_entry.get(&rune_id.store())?.unwrap().value());
      entry.lost = entry.lost.checked_add(lost.n()).unwrap();
      id_to_entry.insert(&rune_id.store(), entry.store())?;
    }

    Ok(())
  }

  fn freeze(
    &mut self,
    tables: &mut Tables,
    txid: Txid,
    runestone: &Runestone,
    unallocated: &HashMap<RuneId, Lot>,
  ) -> Result {
    let Some(edict) = runestone.freeze.clone() else {
      return Ok(());
    };

    for (id, outpoints) in self.get_freezable_balances_by_rune_id(tables, &edict, unallocated)? {
      for outpoint in outpoints {
        self
          .outpoint_to_frozen_rune_id
          .insert(&outpoint.store(), &id.store())?;

        if let Some(sender) = self.event_sender {
          sender.blocking_send(Event::RuneFreezed {
            block_height: self.height,
            outpoint,
            txid,
            rune_id: id,
          })?;
        }
      }
    }

    Ok(())
  }

  fn unfreeze(
    &mut self,
    tables: &mut Tables,
    txid: Txid,
    runestone: &Runestone,
    unallocated: &HashMap<RuneId, Lot>,
  ) -> Result<HashMap<RuneId, Lot>> {
    let mut found: HashMap<RuneId, Lot> = HashMap::new();

    let Some(edict) = runestone.unfreeze.clone() else {
      return Ok(found);
    };

    for (id, outpoints) in self.get_freezable_balances_by_rune_id(tables, &edict, unallocated)? {
      for outpoint in outpoints {
        self
          .outpoint_to_frozen_rune_id
          .remove(&outpoint.store(), &id.store())?;

        if let Some(sender) = self.event_sender {
          sender.blocking_send(Event::RuneUnfreezed {
            block_height: self.height,
            outpoint,
            txid,
            rune_id: id,
          })?;
        }
      }

      // lookup lost balance of id
      let Some(entry) = tables.id_to_entry.get(&id.store())? else {
        continue;
      };

      // include runes lost in this block
      let mut rune_entry = RuneEntry::load(entry.value());
      let lost_in_block = self.lost.entry(id).or_default().0;
      let lost = rune_entry.lost + lost_in_block;

      drop(entry);

      if lost > 0 {
        found.insert(id, Lot(lost));

        // reset lost counter for the current block
        self.lost.insert(id, Lot(0));

        // reset lost counter for entry
        rune_entry.lost = 0;
        tables.id_to_entry.insert(&id.store(), rune_entry.store())?;
      }
    }

    Ok(found)
  }

  fn get_freezable_balances_by_rune_id(
    &self,
    tables: &mut Tables,
    edict: &FreezeEdict,
    unallocated: &HashMap<RuneId, Lot>,
  ) -> Result<HashMap<RuneId, Vec<OutPoint>>> {
    let mut freezables_balances_by_id = HashMap::<RuneId, Vec<OutPoint>>::new();

    // List of outpoints to freeze
    let mut outpoints: Vec<OutPoint> = Vec::new();
    for outpoint_id in &edict.outpoints {
      let Some(outpoint_entry) = tables.outpoint_id_to_outpoint.get(&outpoint_id.store())? else {
        continue;
      };
      outpoints.push(OutPoint::load(outpoint_entry.value()));
    }

    // Add an empty entry for all runes that the unallocated runes can freeze
    if let Some(rune_id) = edict.rune_id {
      // Verify that we possess the rune that can freeze this rune id
      let Some(entry) = tables.id_to_entry.get(&rune_id.store())? else {
        return Ok(freezables_balances_by_id);
      };
      let rune_entry = RuneEntry::load(entry.value());

      let Some(freezer) = rune_entry.freezer else {
        return Ok(freezables_balances_by_id);
      };
      let Some(freezer_rune_id_entry) = tables.rune_to_id.get(&freezer.store())? else {
        return Ok(freezables_balances_by_id);
      };
      let freezer_rune_id = RuneId::load(freezer_rune_id_entry.value());

      // Get the unallocated balance for the freezer rune
      let Some(balance) = unallocated.get(&freezer_rune_id) else {
        return Ok(freezables_balances_by_id);
      };

      // Verify that the freezer rune balance is non-zero
      if *balance > 0 {
        freezables_balances_by_id.insert(rune_id, Vec::new());
      }
    } else {
      // Add all runes that our input runes can freeze
      for (id, balance) in unallocated {
        if *balance > 0 {
          // Lookup rune
          let Some(entry) = tables.id_to_entry.get(&id.store())? else {
            continue;
          };
          let rune_entry = RuneEntry::load(entry.value());

          // Lookup rune ids that can be freezed by this rune
          let freezable_ids = tables
            .rune_to_freezable_rune_id
            .get(rune_entry.spaced_rune.rune.store())?
            .filter_map(|rune_id| {
              let guard = rune_id.ok()?;
              Some(RuneId::load(guard.value()))
            })
            .collect::<Vec<RuneId>>();

          freezables_balances_by_id.extend(freezable_ids.into_iter().map(|id| (id, Vec::new())));
        }
      }
    }

    // Add outpoint balances to map if freezable
    for outpoint in outpoints {
      let Some(guard) = tables.outpoint_to_balances.get(&outpoint.store())? else {
        continue;
      };

      let buffer = guard.value();
      let mut i = 0;
      while i < buffer.len() {
        let ((id, balance), len) = Index::decode_rune_balance(&buffer[i..]).unwrap();
        i += len;

        if balance > 0 {
          freezables_balances_by_id
            .entry(id)
            .and_modify(|balances| balances.push(outpoint));
        }
      }
    }

    Ok(freezables_balances_by_id)
  }
}
