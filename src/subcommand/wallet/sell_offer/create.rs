use {
  super::*, bitcoin::sighash::EcdsaSighashType::SinglePlusAnyoneCanPay,
  bitcoincore_rpc::json::SigHashType,
};

#[derive(Debug, Serialize, Deserialize)]
pub struct Output {
  pub psbt: String,
  pub outgoing: Vec<Outgoing>,
}

#[derive(Debug, Parser)]
pub(crate) struct Create {
  #[arg(long, help = "<INSCRIPTION> or <DECIMAL:RUNE> to make offer for.")]
  outgoing: Vec<Outgoing>,
  #[arg(long, help = "<AMOUNT> to offer.")]
  amount: Amount,
}

impl Create {
  pub(crate) fn run(&self, wallet: Wallet) -> SubcommandResult {
    ensure! {
      self.outgoing.len() == 1,
      "multiple outgoings not yet supported"
    }

    let psbt = match self.outgoing[0] {
      Outgoing::Rune { decimal, rune } => self.create_rune_sell_offer(wallet, decimal, rune)?,
      Outgoing::InscriptionId(_) => bail!("inscription sell offers not yet implemented"),
      _ => bail!("outgoing must be either <INSCRIPTION> or <DECIMAL:RUNE>"),
    };

    Ok(Some(Box::new(Output {
      psbt,
      outgoing: self.outgoing.clone(),
    })))
  }

  fn create_rune_sell_offer(
    &self,
    wallet: Wallet,
    decimal: Decimal,
    spaced_rune: SpacedRune,
  ) -> Result<String> {
    ensure!(
      wallet.has_rune_index(),
      "creating runes offer with `ord offer` requires index created with `--index-runes` flag",
    );

    wallet.lock_non_cardinal_outputs()?;

    let (_id, entry, _parent) = wallet
      .get_rune(spaced_rune.rune)?
      .with_context(|| format!("rune `{}` has not been etched", spaced_rune.rune))?;

    let amount = decimal.to_integer(entry.divisibility)?;

    let inscribed_outputs = wallet
      .inscriptions()
      .keys()
      .map(|satpoint| satpoint.outpoint)
      .collect::<HashSet<OutPoint>>();

    let balances = wallet
      .get_runic_outputs()?
      .unwrap_or_default()
      .into_iter()
      .filter(|output| !inscribed_outputs.contains(output))
      .map(|output| {
        wallet.get_runes_balances_in_output(&output).map(|balance| {
          (
            output,
            balance
              .unwrap_or_default()
              .into_iter()
              .map(|(spaced_rune, pile)| (spaced_rune.rune, pile.amount))
              .collect(),
          )
        })
      })
      .collect::<Result<BTreeMap<OutPoint, BTreeMap<Rune, u128>>>>()?;

    let mut input = None;
    for (output, runes) in balances {
      if let Some(balance) = runes.get(&spaced_rune.rune) {
        if *balance == amount && runes.len() == 1 {
          input = Some(output);
          break;
        }
      }
    }

    let Some(input) = input else {
      bail!(
        "missing outpoint with exact `{}:{}` balance in wallet",
        decimal,
        spaced_rune
      );
    };

    let postage = Amount::from_sat(wallet.get_value_in_output(&input)?);

    let tx = Transaction {
      version: Version(2),
      lock_time: LockTime::ZERO,
      input: vec![TxIn {
        previous_output: input,
        script_sig: ScriptBuf::new(),
        sequence: Sequence::ENABLE_RBF_NO_LOCKTIME,
        witness: Witness::new(),
      }],
      output: vec![TxOut {
        value: self.amount + postage,
        script_pubkey: wallet.get_change_address()?.into(),
      }],
    };

    let psbt = Psbt::from_unsigned_tx(tx)?;

    let result = wallet
      .bitcoin_client()
      .call::<String>("utxoupdatepsbt", &[base64_encode(&psbt.serialize()).into()])?;

    let result = wallet.bitcoin_client().wallet_process_psbt(
      &result,
      Some(true),
      Some(SigHashType::from(SinglePlusAnyoneCanPay)),
      None,
    )?;

    ensure! {
      result.complete,
      "Failed to sign PSBT after processing with wallet",
    }

    Ok(result.psbt)
  }
}
