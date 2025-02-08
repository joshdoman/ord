use super::*;

pub(super) struct RuneUpdater<'a, 'tx, 'client> {
  pub(super) block_time: u32,
  pub(super) burned: HashMap<RuneId, Lot>,
  pub(super) lost: HashMap<RuneId, Lot>,
  pub(super) client: &'client Client,
  pub(super) event_sender: Option<&'a mpsc::Sender<Event>>,
  pub(super) height: u32,
  pub(super) id_to_entry: &'a mut Table<'tx, RuneIdValue, RuneEntryValue>,
  pub(super) inscription_id_to_sequence_number: &'a Table<'tx, InscriptionIdValue, u32>,
  pub(super) minimum: Rune,
  pub(super) rune_to_freezable_rune_id: &'a mut MultimapTable<'tx, u128, RuneIdValue>,
  pub(super) outpoint_id_to_outpoint: &'a mut Table<'tx, OutPointIdValue, OutPointValue>,
  pub(super) outpoint_to_outpoint_id: &'a mut Table<'tx, &'static OutPointValue, OutPointIdValue>,
  pub(super) outpoint_to_balances: &'a mut Table<'tx, &'static OutPointValue, &'static [u8]>,
  pub(super) outpoint_to_frozen_rune_id:
    &'a mut MultimapTable<'tx, &'static OutPointValue, RuneIdValue>,
  pub(super) rune_to_id: &'a mut Table<'tx, u128, RuneIdValue>,
  pub(super) runes: u64,
  pub(super) sequence_number_to_rune_id: &'a mut Table<'tx, u32, RuneIdValue>,
  pub(super) statistic_to_count: &'a mut Table<'tx, u64, u64>,
  pub(super) transaction_id_to_rune: &'a mut Table<'tx, &'static TxidValue, u128>,
}

impl RuneUpdater<'_, '_, '_> {
  pub(super) fn index_runes(&mut self, tx_index: u32, tx: &Transaction, txid: Txid) -> Result<()> {
    let artifact = Runestone::decipher(tx);

    let mut unallocated = self.unallocated(tx, txid)?;

    let mut allocated: Vec<HashMap<RuneId, Lot>> = vec![HashMap::new(); tx.output.len()];

    if let Some(artifact) = &artifact {
      if let Some(id) = artifact.mint() {
        if let Some(amount) = self.mint(id)? {
          *unallocated.entry(id).or_default() += amount;

          if let Some(sender) = self.event_sender {
            sender.blocking_send(Event::RuneMinted {
              block_height: self.height,
              txid,
              rune_id: id,
              amount: amount.n(),
            })?;
          }
        }
      }

      let etched = self.etched(tx_index, tx, artifact)?;

      if let Artifact::Runestone(runestone) = artifact {
        if let Some((id, ..)) = etched {
          *unallocated.entry(id).or_default() +=
            runestone.etching.unwrap().premine.unwrap_or_default();
        }

        self.freeze(txid, runestone, &unallocated)?;
        self.unfreeze(txid, runestone, &unallocated)?;

        for Edict { id, amount, output } in runestone.edicts.iter().copied() {
          let amount = Lot(amount);

          // edicts with output values greater than the number of outputs
          // should never be produced by the edict parser
          let output = usize::try_from(output).unwrap();
          assert!(output <= tx.output.len());

          let id = if id == RuneId::default() {
            let Some((id, ..)) = etched else {
              continue;
            };

            id
          } else {
            id
          };

          let Some(balance) = unallocated.get_mut(&id) else {
            continue;
          };

          let mut allocate = |balance: &mut Lot, amount: Lot, output: usize| {
            if amount > 0 {
              *balance -= amount;
              *allocated[output].entry(id).or_default() += amount;
            }
          };

          if output == tx.output.len() {
            // find non-OP_RETURN outputs
            let destinations = tx
              .output
              .iter()
              .enumerate()
              .filter_map(|(output, tx_out)| {
                (!tx_out.script_pubkey.is_op_return()).then_some(output)
              })
              .collect::<Vec<usize>>();

            if !destinations.is_empty() {
              if amount == 0 {
                // if amount is zero, divide balance between eligible outputs
                let amount = *balance / destinations.len() as u128;
                let remainder = usize::try_from(*balance % destinations.len() as u128).unwrap();

                for (i, output) in destinations.iter().enumerate() {
                  allocate(
                    balance,
                    if i < remainder { amount + 1 } else { amount },
                    *output,
                  );
                }
              } else {
                // if amount is non-zero, distribute amount to eligible outputs
                for output in destinations {
                  allocate(balance, amount.min(*balance), output);
                }
              }
            }
          } else {
            // Get the allocatable amount
            let amount = if amount == 0 {
              *balance
            } else {
              amount.min(*balance)
            };

            allocate(balance, amount, output);
          }
        }
      }

      if let Some((id, rune)) = etched {
        self.create_rune_entry(txid, artifact, id, rune)?;
      }
    }

    let mut burned: HashMap<RuneId, Lot> = HashMap::new();

    if let Some(Artifact::Cenotaph(_)) = artifact {
      for (id, balance) in unallocated {
        *burned.entry(id).or_default() += balance;
      }
    } else {
      let pointer = artifact
        .map(|artifact| match artifact {
          Artifact::Runestone(runestone) => runestone.pointer,
          Artifact::Cenotaph(_) => unreachable!(),
        })
        .unwrap_or_default();

      // assign all un-allocated runes to the default output, or the first non
      // OP_RETURN output if there is no default
      if let Some(vout) = pointer
        .map(|pointer| pointer.into_usize())
        .inspect(|&pointer| assert!(pointer < allocated.len()))
        .or_else(|| {
          tx.output
            .iter()
            .enumerate()
            .find(|(_vout, tx_out)| !tx_out.script_pubkey.is_op_return())
            .map(|(vout, _tx_out)| vout)
        })
      {
        for (id, balance) in unallocated {
          if balance > 0 {
            *allocated[vout].entry(id).or_default() += balance;
          }
        }
      } else {
        for (id, balance) in unallocated {
          if balance > 0 {
            *burned.entry(id).or_default() += balance;
          }
        }
      }
    }

    // update outpoint balances
    let mut buffer: Vec<u8> = Vec::new();
    for (vout, balances) in allocated.into_iter().enumerate() {
      if balances.is_empty() {
        continue;
      }

      // increment burned balances
      if tx.output[vout].script_pubkey.is_op_return() {
        for (id, balance) in &balances {
          *burned.entry(*id).or_default() += *balance;
        }
        continue;
      }

      buffer.clear();

      let mut balances = balances.into_iter().collect::<Vec<(RuneId, Lot)>>();

      // Sort balances by id so tests can assert balances in a fixed order
      balances.sort();

      let outpoint = OutPoint {
        txid,
        vout: vout.try_into().unwrap(),
      };

      for (id, balance) in balances {
        Index::encode_rune_balance(id, balance.n(), &mut buffer);

        if let Some(sender) = self.event_sender {
          sender.blocking_send(Event::RuneTransferred {
            outpoint,
            block_height: self.height,
            txid,
            rune_id: id,
            amount: balance.0,
          })?;
        }
      }

      let outpoint_id = OutPointId {
        block: self.height.into(),
        tx: tx_index,
        output: outpoint.vout,
      };
      self
        .outpoint_id_to_outpoint
        .insert(outpoint_id.store(), outpoint.store())?;
      self
        .outpoint_to_outpoint_id
        .insert(&outpoint.store(), outpoint_id.store())?;
      self
        .outpoint_to_balances
        .insert(&outpoint.store(), buffer.as_slice())?;
    }

    // increment entries with burned runes
    for (id, amount) in burned {
      *self.burned.entry(id).or_default() += amount;

      if let Some(sender) = self.event_sender {
        sender.blocking_send(Event::RuneBurned {
          block_height: self.height,
          txid,
          rune_id: id,
          amount: amount.n(),
        })?;
      }
    }

    Ok(())
  }

  pub(super) fn update(self) -> Result {
    for (rune_id, burned) in self.burned {
      let mut entry = RuneEntry::load(self.id_to_entry.get(&rune_id.store())?.unwrap().value());
      entry.burned = entry.burned.checked_add(burned.n()).unwrap();
      self.id_to_entry.insert(&rune_id.store(), entry.store())?;
    }

    for (rune_id, lost) in self.lost {
      let mut entry = RuneEntry::load(self.id_to_entry.get(&rune_id.store())?.unwrap().value());
      entry.lost = entry.lost.checked_add(lost.n()).unwrap();
      self.id_to_entry.insert(&rune_id.store(), entry.store())?;
    }

    Ok(())
  }

  fn freeze(
    &mut self,
    txid: Txid,
    runestone: &Runestone,
    unallocated: &HashMap<RuneId, Lot>,
  ) -> Result {
    let Some(edict) = runestone.freeze.clone() else {
      return Ok(());
    };

    for (outpoint, id) in self.get_freezable_outpoint_balances(&edict, unallocated)? {
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

    Ok(())
  }

  fn unfreeze(
    &mut self,
    txid: Txid,
    runestone: &Runestone,
    unallocated: &HashMap<RuneId, Lot>,
  ) -> Result {
    let Some(edict) = runestone.unfreeze.clone() else {
      return Ok(());
    };

    for (outpoint, id) in self.get_freezable_outpoint_balances(&edict, unallocated)? {
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

    Ok(())
  }

  fn get_freezable_outpoint_balances(
    &mut self,
    edict: &FreezeEdict,
    unallocated: &HashMap<RuneId, Lot>,
  ) -> Result<Vec<(OutPoint, RuneId)>> {
    let mut freezable_balances = Vec::new();

    // List of outpoints to freeze
    let mut outpoints: Vec<OutPoint> = Vec::new();
    for outpoint_id in &edict.outpoints {
      let Some(outpoint_entry) = self.outpoint_id_to_outpoint.get(&outpoint_id.store())? else {
        continue;
      };
      outpoints.push(OutPoint::load(outpoint_entry.value()));
    }

    // List runes that the the unallocated runes can freeze
    let mut runes_to_freeze: Vec<RuneId> = Vec::new();
    if let Some(rune_id) = edict.rune_id {
      // Verify that we possess the rune that can freeze this rune id
      let Some(entry) = self.id_to_entry.get(&rune_id.store())? else {
        return Ok(freezable_balances);
      };
      let rune_entry = RuneEntry::load(entry.value());

      let Some(freezer) = rune_entry.freezer else {
        return Ok(freezable_balances);
      };
      let Some(freezer_rune_id_entry) = self.rune_to_id.get(&freezer.store())? else {
        return Ok(freezable_balances);
      };
      let freezer_rune_id = RuneId::load(freezer_rune_id_entry.value());

      // Get the unallocated balance for the freezer rune
      let Some(balance) = unallocated.get(&freezer_rune_id) else {
        return Ok(freezable_balances);
      };

      // Verify that the freezer rune balance is non-zero
      if *balance > 0 {
        runes_to_freeze.push(rune_id);
      }
    } else {
      // Add all runes that our input runes can freeze
      for (id, balance) in unallocated {
        if *balance > 0 {
          // Lookup rune
          let Some(entry) = self.id_to_entry.get(&id.store())? else {
            continue;
          };
          let rune_entry = RuneEntry::load(entry.value());

          // Lookup rune ids that can be freezed by this rune
          let freezable_ids = self
            .rune_to_freezable_rune_id
            .get(rune_entry.spaced_rune.rune.store())?
            .filter_map(|rune_id| {
              let guard = rune_id.ok()?;
              Some(RuneId::load(guard.value()))
            })
            .collect::<Vec<RuneId>>();
          runes_to_freeze.extend(freezable_ids);
        }
      }
    }

    // Mark outpoint balances as freezable
    for outpoint in outpoints {
      // Get the runes at this outpoint
      let mut outpoint_runes: HashSet<RuneId> = HashSet::new();

      let Some(guard) = self.outpoint_to_balances.get(&outpoint.store())? else {
        continue;
      };

      let buffer = guard.value();
      let mut i = 0;
      while i < buffer.len() {
        let ((id, balance), len) = Index::decode_rune_balance(&buffer[i..]).unwrap();
        i += len;

        if balance > 0 {
          outpoint_runes.insert(id);
        }
      }

      // Add the freezable runes at this outpoint to the list of freezable balances
      for id in &runes_to_freeze {
        if outpoint_runes.contains(id) {
          freezable_balances.push((outpoint, *id));
        }
      }
    }

    Ok(freezable_balances)
  }

  fn create_rune_entry(
    &mut self,
    txid: Txid,
    artifact: &Artifact,
    id: RuneId,
    rune: Rune,
  ) -> Result {
    self.rune_to_id.insert(rune.store(), id.store())?;
    self
      .transaction_id_to_rune
      .insert(&txid.store(), rune.store())?;

    let number = self.runes;
    self.runes += 1;

    self
      .statistic_to_count
      .insert(&Statistic::Runes.into(), self.runes)?;

    let entry = match artifact {
      Artifact::Cenotaph(_) => RuneEntry {
        block: id.block,
        burned: 0,
        lost: 0,
        divisibility: 0,
        etching: txid,
        terms: None,
        mints: 0,
        number,
        premine: 0,
        spaced_rune: SpacedRune { rune, spacers: 0 },
        symbol: None,
        timestamp: self.block_time.into(),
        turbo: false,
        freezer: None,
      },
      Artifact::Runestone(Runestone { etching, .. }) => {
        let Etching {
          divisibility,
          terms,
          premine,
          spacers,
          symbol,
          turbo,
          freezer,
          ..
        } = etching.unwrap();

        RuneEntry {
          block: id.block,
          burned: 0,
          lost: 0,
          divisibility: divisibility.unwrap_or_default(),
          etching: txid,
          terms,
          mints: 0,
          number,
          premine: premine.unwrap_or_default(),
          spaced_rune: SpacedRune {
            rune,
            spacers: spacers.unwrap_or_default(),
          },
          symbol,
          timestamp: self.block_time.into(),
          turbo,
          freezer,
        }
      }
    };

    self.id_to_entry.insert(id.store(), entry.store())?;

    if let Some(freezer) = entry.freezer {
      self
        .rune_to_freezable_rune_id
        .insert(freezer.0, id.store())?;
    }

    if let Some(sender) = self.event_sender {
      sender.blocking_send(Event::RuneEtched {
        block_height: self.height,
        txid,
        rune_id: id,
      })?;
    }

    let inscription_id = InscriptionId { txid, index: 0 };

    if let Some(sequence_number) = self
      .inscription_id_to_sequence_number
      .get(&inscription_id.store())?
    {
      self
        .sequence_number_to_rune_id
        .insert(sequence_number.value(), id.store())?;
    }

    Ok(())
  }

  fn etched(
    &mut self,
    tx_index: u32,
    tx: &Transaction,
    artifact: &Artifact,
  ) -> Result<Option<(RuneId, Rune)>> {
    let rune = match artifact {
      Artifact::Runestone(runestone) => match runestone.etching {
        Some(etching) => etching.rune,
        None => return Ok(None),
      },
      Artifact::Cenotaph(cenotaph) => match cenotaph.etching {
        Some(rune) => Some(rune),
        None => return Ok(None),
      },
    };

    let rune = if let Some(rune) = rune {
      if rune < self.minimum
        || rune.is_reserved()
        || self.rune_to_id.get(rune.0)?.is_some()
        || !self.tx_commits_to_rune(tx, rune)?
      {
        return Ok(None);
      }
      rune
    } else {
      let reserved_runes = self
        .statistic_to_count
        .get(&Statistic::ReservedRunes.into())?
        .map(|entry| entry.value())
        .unwrap_or_default();

      self
        .statistic_to_count
        .insert(&Statistic::ReservedRunes.into(), reserved_runes + 1)?;

      Rune::reserved(self.height.into(), tx_index)
    };

    Ok(Some((
      RuneId {
        block: self.height.into(),
        tx: tx_index,
      },
      rune,
    )))
  }

  fn mint(&mut self, id: RuneId) -> Result<Option<Lot>> {
    let Some(entry) = self.id_to_entry.get(&id.store())? else {
      return Ok(None);
    };

    let mut rune_entry = RuneEntry::load(entry.value());

    let Ok(amount) = rune_entry.mintable(self.height.into()) else {
      return Ok(None);
    };

    drop(entry);

    rune_entry.mints += 1;

    self.id_to_entry.insert(&id.store(), rune_entry.store())?;

    Ok(Some(Lot(amount)))
  }

  fn tx_commits_to_rune(&self, tx: &Transaction, rune: Rune) -> Result<bool> {
    let commitment = rune.commitment();

    for input in &tx.input {
      // extracting a tapscript does not indicate that the input being spent
      // was actually a taproot output. this is checked below, when we load the
      // output's entry from the database
      let Some(tapscript) = input.witness.tapscript() else {
        continue;
      };

      for instruction in tapscript.instructions() {
        // ignore errors, since the extracted script may not be valid
        let Ok(instruction) = instruction else {
          break;
        };

        let Some(pushbytes) = instruction.push_bytes() else {
          continue;
        };

        if pushbytes.as_bytes() != commitment {
          continue;
        }

        let Some(tx_info) = self
          .client
          .get_raw_transaction_info(&input.previous_output.txid, None)
          .into_option()?
        else {
          panic!(
            "can't get input transaction: {}",
            input.previous_output.txid
          );
        };

        let taproot = tx_info.vout[input.previous_output.vout.into_usize()]
          .script_pub_key
          .script()?
          .is_p2tr();

        if !taproot {
          continue;
        }

        let commit_tx_height = self
          .client
          .get_block_header_info(&tx_info.blockhash.unwrap())
          .into_option()?
          .unwrap()
          .height;

        let confirmations = self
          .height
          .checked_sub(commit_tx_height.try_into().unwrap())
          .unwrap()
          + 1;

        if confirmations >= Runestone::COMMIT_CONFIRMATIONS.into() {
          return Ok(true);
        }
      }
    }

    Ok(false)
  }

  fn unallocated(&mut self, tx: &Transaction, txid: Txid) -> Result<HashMap<RuneId, Lot>> {
    // map of rune ID to un-allocated balance of that rune
    let mut unallocated: HashMap<RuneId, Lot> = HashMap::new();

    // increment unallocated runes with the runes in tx inputs
    for input in &tx.input {
      if let Some(guard) = self
        .outpoint_to_balances
        .remove(&input.previous_output.store())?
      {
        let frozen_runes = self
          .outpoint_to_frozen_rune_id
          .remove_all(&input.previous_output.store())?
          .filter_map(|rune_id| {
            let guard = rune_id.ok()?;
            Some(RuneId::load(guard.value()))
          })
          .collect::<HashSet<RuneId>>();

        let buffer = guard.value();
        let mut i = 0;
        while i < buffer.len() {
          let ((id, balance), len) = Index::decode_rune_balance(&buffer[i..]).unwrap();
          i += len;

          if frozen_runes.contains(&id) {
            // Mark rune as lost if transferred while frozen
            *self.lost.entry(id).or_default() += balance;

            if let Some(sender) = self.event_sender {
              sender.blocking_send(Event::RuneLost {
                block_height: self.height,
                txid,
                rune_id: id,
                amount: balance,
                outpoint: input.previous_output,
              })?;
            }
          } else {
            *unallocated.entry(id).or_default() += balance;
          }
        }

        // Remove outpoint id mappings
        if let Some(outpoint_id) = self
          .outpoint_to_outpoint_id
          .remove(&input.previous_output.store())?
        {
          self.outpoint_id_to_outpoint.remove(outpoint_id.value())?;
        }
      }
    }

    Ok(unallocated)
  }
}
