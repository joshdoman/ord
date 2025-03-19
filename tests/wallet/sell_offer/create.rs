use super::*;

type Create = ord::subcommand::wallet::sell_offer::create::Output;

#[test]
fn single_input_rune_sell_offer() {
  let core = mockcore::builder().network(Network::Regtest).build();

  let ord = TestServer::spawn_with_server_args(&core, &["--index-runes", "--regtest"], &[]);

  create_wallet(&core, &ord);

  let rune = Rune(RUNE);
  let a = etch(&core, &ord, rune);

  core.mine_blocks(1);

  let create = CommandBuilder::new(format!(
    "--regtest wallet sell-offer create --outgoing 1000:{rune} --amount 1btc",
  ))
  .core(&core)
  .ord(&ord)
  .run_and_deserialize_output::<Create>();

  assert_eq!(
    create.outgoing,
    Outgoing::Rune {
      rune: SpacedRune { rune, spacers: 0 },
      decimal: "1000".parse().unwrap(),
    }
  );

  assert_eq!(create.amount, Amount::from_sat(100_000_000));

  assert!(!create.has_multiple);
  assert!(!create.is_partial);

  let outputs = CommandBuilder::new("--regtest wallet outputs")
    .core(&core)
    .ord(&ord)
    .run_and_deserialize_output::<Vec<ord::subcommand::wallet::outputs::Output>>();

  let psbt = Psbt::deserialize(&base64_decode(&create.psbt).unwrap()).unwrap();

  assert_eq!(psbt.unsigned_tx.input.len(), 1);
  assert_eq!(psbt.unsigned_tx.output.len(), 1);

  assert!(outputs
    .iter()
    .any(|output| output.output == psbt.unsigned_tx.input[0].previous_output));

  assert!(core.state().is_wallet_address(
    &Address::from_script(&psbt.unsigned_tx.output[0].script_pubkey, Network::Regtest).unwrap()
  ));

  // verify input is signed with SINGLE|ANYONECANPAY
  assert_eq!(
    psbt.inputs[0].final_script_witness,
    Some(Witness::from_slice(&[&[1; 64]]))
  );

  pretty_assertions::assert_eq!(
    psbt.unsigned_tx,
    Transaction {
      version: Version(2),
      lock_time: LockTime::ZERO,
      input: vec![TxIn {
        previous_output: OutPoint {
          txid: a.output.reveal,
          vout: 1,
        },
        script_sig: ScriptBuf::new(),
        sequence: Sequence::ENABLE_RBF_NO_LOCKTIME,
        witness: Witness::new(),
      }],
      output: vec![TxOut {
        value: Amount::from_sat(100_010_000),
        script_pubkey: psbt.unsigned_tx.output[0].script_pubkey.clone(),
      }],
    }
  );
}

#[test]
fn multi_input_rune_sell_offer() {
  let core = mockcore::builder().network(Network::Regtest).build();

  let ord = TestServer::spawn_with_server_args(&core, &["--index-runes", "--regtest"], &[]);

  create_wallet(&core, &ord);

  let rune = Rune(RUNE);
  etch(&core, &ord, rune);

  core.mine_blocks(1);

  let address = core.state().new_address(false);

  let send = CommandBuilder::new(format!(
    "--regtest wallet send --fee-rate 0 {address} 500:{rune}"
  ))
  .core(&core)
  .ord(&ord)
  .run_and_deserialize_output::<Send>();

  core.mine_blocks(1);

  let create = CommandBuilder::new(format!(
    "--regtest wallet sell-offer create --outgoing {}:{} --amount 1btc --allow-multiple-utxos",
    1000,
    Rune(RUNE),
  ))
  .core(&core)
  .ord(&ord)
  .run_and_deserialize_output::<Create>();

  assert_eq!(
    create.outgoing,
    Outgoing::Rune {
      rune: SpacedRune { rune, spacers: 0 },
      decimal: "1000".parse().unwrap(),
    }
  );

  assert_eq!(create.amount, Amount::from_sat(100_000_000));

  assert!(create.has_multiple);
  assert!(!create.is_partial);

  let outputs = CommandBuilder::new("--regtest wallet outputs")
    .core(&core)
    .ord(&ord)
    .run_and_deserialize_output::<Vec<ord::subcommand::wallet::outputs::Output>>();

  let psbt = Psbt::deserialize(&base64_decode(&create.psbt).unwrap()).unwrap();

  assert_eq!(psbt.unsigned_tx.input.len(), 2);
  assert_eq!(psbt.unsigned_tx.output.len(), 2);

  for i in 0..2 {
    assert!(outputs
      .iter()
      .any(|output| output.output == psbt.unsigned_tx.input[i].previous_output));

    assert!(core.state().is_wallet_address(
      &Address::from_script(&psbt.unsigned_tx.output[i].script_pubkey, Network::Regtest).unwrap()
    ));

    // verify input is signed with SINGLE|ANYONECANPAY
    assert_eq!(
      psbt.inputs[i].final_script_witness,
      Some(Witness::from_slice(&[&[1; 64]]))
    );
  }

  pretty_assertions::assert_eq!(
    psbt.unsigned_tx,
    Transaction {
      version: Version(2),
      lock_time: LockTime::ZERO,
      input: vec![
        TxIn {
          previous_output: OutPoint {
            txid: send.txid,
            vout: 2,
          },
          script_sig: ScriptBuf::new(),
          sequence: Sequence::ENABLE_RBF_NO_LOCKTIME,
          witness: Witness::new(),
        },
        TxIn {
          previous_output: OutPoint {
            txid: send.txid,
            vout: 1,
          },
          script_sig: ScriptBuf::new(),
          sequence: Sequence::ENABLE_RBF_NO_LOCKTIME,
          witness: Witness::new(),
        }
      ],
      output: vec![
        TxOut {
          value: Amount::from_sat(50_010_000),
          script_pubkey: psbt.unsigned_tx.output[0].script_pubkey.clone(),
        },
        TxOut {
          value: Amount::from_sat(50_010_000),
          script_pubkey: psbt.unsigned_tx.output[1].script_pubkey.clone(),
        }
      ],
    }
  );
}

#[test]
fn multi_unequal_input_rune_sell_offer_with_rounding() {
  let core = mockcore::builder().network(Network::Regtest).build();

  let ord = TestServer::spawn_with_server_args(&core, &["--index-runes", "--regtest"], &[]);

  create_wallet(&core, &ord);

  batch(
    &core,
    &ord,
    batch::File {
      etching: Some(batch::Etching {
        divisibility: 0,
        rune: SpacedRune {
          rune: Rune(RUNE),
          spacers: 0,
        },
        premine: "0".parse().unwrap(),
        supply: "3000".parse().unwrap(),
        symbol: '¢',
        terms: Some(batch::Terms {
          cap: 3,
          offset: None,
          amount: "1000".parse().unwrap(),
          height: None,
        }),
        turbo: false,
      }),
      inscriptions: vec![batch::Entry {
        file: Some("inscription.jpeg".into()),
        ..default()
      }],
      ..default()
    },
  );

  let mint0 = CommandBuilder::new(format!(
    "--regtest wallet mint --fee-rate 1 --rune {}",
    Rune(RUNE)
  ))
  .core(&core)
  .ord(&ord)
  .run_and_deserialize_output::<ord::subcommand::wallet::mint::Output>();

  core.mine_blocks(1);

  let mint1 = CommandBuilder::new(format!(
    "--regtest wallet mint --fee-rate 1 --rune {}",
    Rune(RUNE)
  ))
  .core(&core)
  .ord(&ord)
  .run_and_deserialize_output::<ord::subcommand::wallet::mint::Output>();

  core.mine_blocks(1);

  CommandBuilder::new(format!(
    "--regtest wallet mint --fee-rate 1 --rune {}",
    Rune(RUNE)
  ))
  .core(&core)
  .ord(&ord)
  .run_and_deserialize_output::<ord::subcommand::wallet::mint::Output>();

  core.mine_blocks(1);

  let send = CommandBuilder::new(format!(
    "
      --chain regtest
      wallet
      send
      --fee-rate 1
      bcrt1qs758ursh4q9z627kt3pp5yysm78ddny6txaqgw 750:{}
    ",
    Rune(RUNE),
  ))
  .core(&core)
  .ord(&ord)
  .run_and_deserialize_output::<Send>();

  core.mine_blocks(1);

  let create = CommandBuilder::new(format!(
    "--regtest wallet sell-offer create --outgoing {}:{} --amount 1btc --allow-multiple-utxos",
    2250,
    Rune(RUNE),
  ))
  .core(&core)
  .ord(&ord)
  .run_and_deserialize_output::<Create>();

  assert_eq!(
    create.outgoing,
    Outgoing::Rune {
      rune: SpacedRune {
        rune: Rune(RUNE),
        spacers: 0,
      },
      decimal: "2250".parse().unwrap(),
    }
  );

  assert_eq!(create.amount, Amount::from_sat(100_000_002));

  assert!(create.has_multiple);
  assert!(!create.is_partial);

  let outputs = CommandBuilder::new("--regtest wallet outputs")
    .core(&core)
    .ord(&ord)
    .run_and_deserialize_output::<Vec<ord::subcommand::wallet::outputs::Output>>();

  let psbt = Psbt::deserialize(&base64_decode(&create.psbt).unwrap()).unwrap();

  assert_eq!(psbt.unsigned_tx.input.len(), 3);
  assert_eq!(psbt.unsigned_tx.output.len(), 3);

  for i in 0..3 {
    assert!(outputs
      .iter()
      .any(|output| output.output == psbt.unsigned_tx.input[i].previous_output));

    assert!(core.state().is_wallet_address(
      &Address::from_script(&psbt.unsigned_tx.output[i].script_pubkey, Network::Regtest).unwrap()
    ));

    // verify input is signed with SINGLE|ANYONECANPAY
    assert_eq!(
      psbt.inputs[i].final_script_witness,
      Some(Witness::from_slice(&[&[1; 64]]))
    );
  }

  pretty_assertions::assert_eq!(
    psbt.unsigned_tx,
    Transaction {
      version: Version(2),
      lock_time: LockTime::ZERO,
      input: vec![
        TxIn {
          previous_output: OutPoint {
            txid: send.txid,
            vout: 1,
          },
          script_sig: ScriptBuf::new(),
          sequence: Sequence::ENABLE_RBF_NO_LOCKTIME,
          witness: Witness::new(),
        },
        TxIn {
          previous_output: OutPoint {
            txid: mint0.mint,
            vout: 1,
          },
          script_sig: ScriptBuf::new(),
          sequence: Sequence::ENABLE_RBF_NO_LOCKTIME,
          witness: Witness::new(),
        },
        TxIn {
          previous_output: OutPoint {
            txid: mint1.mint,
            vout: 1,
          },
          script_sig: ScriptBuf::new(),
          sequence: Sequence::ENABLE_RBF_NO_LOCKTIME,
          witness: Witness::new(),
        }
      ],
      output: vec![
        TxOut {
          value: Amount::from_sat(11_121_112),
          script_pubkey: psbt.unsigned_tx.output[0].script_pubkey.clone(),
        },
        TxOut {
          value: Amount::from_sat(44_454_445),
          script_pubkey: psbt.unsigned_tx.output[1].script_pubkey.clone(),
        },
        TxOut {
          value: Amount::from_sat(44_454_445),
          script_pubkey: psbt.unsigned_tx.output[2].script_pubkey.clone(),
        },
      ],
    }
  );
}

#[test]
fn single_input_rune_partial_sell_offer() {
  let core = mockcore::builder().network(Network::Regtest).build();

  let ord = TestServer::spawn_with_server_args(&core, &["--index-runes", "--regtest"], &[]);

  create_wallet(&core, &ord);

  etch(&core, &ord, Rune(RUNE));

  let send = CommandBuilder::new(format!(
    "
      --chain regtest
      wallet
      send
      --fee-rate 1
      bcrt1qs758ursh4q9z627kt3pp5yysm78ddny6txaqgw 750:{}
    ",
    Rune(RUNE),
  ))
  .core(&core)
  .ord(&ord)
  .run_and_deserialize_output::<Send>();

  core.mine_blocks(1);

  let create = CommandBuilder::new(format!(
    "--regtest wallet sell-offer create --outgoing {}:{} --amount 1btc --allow-partial",
    500,
    Rune(RUNE),
  ))
  .core(&core)
  .ord(&ord)
  .run_and_deserialize_output::<Create>();

  assert_eq!(
    create.outgoing,
    Outgoing::Rune {
      rune: SpacedRune {
        rune: Rune(RUNE),
        spacers: 0,
      },
      decimal: "250".parse().unwrap(),
    }
  );

  assert_eq!(create.amount, Amount::from_sat(50_000_000));

  assert!(!create.has_multiple);
  assert!(create.is_partial);

  let outputs = CommandBuilder::new("--regtest wallet outputs")
    .core(&core)
    .ord(&ord)
    .run_and_deserialize_output::<Vec<ord::subcommand::wallet::outputs::Output>>();

  let psbt = Psbt::deserialize(&base64_decode(&create.psbt).unwrap()).unwrap();

  assert_eq!(psbt.unsigned_tx.input.len(), 1);
  assert_eq!(psbt.unsigned_tx.output.len(), 1);

  assert!(outputs
    .iter()
    .any(|output| output.output == psbt.unsigned_tx.input[0].previous_output));

  assert!(core.state().is_wallet_address(
    &Address::from_script(&psbt.unsigned_tx.output[0].script_pubkey, Network::Regtest).unwrap()
  ));

  // verify input is signed with SINGLE|ANYONECANPAY
  assert_eq!(
    psbt.inputs[0].final_script_witness,
    Some(Witness::from_slice(&[&[1; 64]]))
  );

  pretty_assertions::assert_eq!(
    psbt.unsigned_tx,
    Transaction {
      version: Version(2),
      lock_time: LockTime::ZERO,
      input: vec![TxIn {
        previous_output: OutPoint {
          txid: send.txid,
          vout: 1,
        },
        script_sig: ScriptBuf::new(),
        sequence: Sequence::ENABLE_RBF_NO_LOCKTIME,
        witness: Witness::new(),
      }],
      output: vec![TxOut {
        value: Amount::from_sat(50_010_000),
        script_pubkey: psbt.unsigned_tx.output[0].script_pubkey.clone(),
      }],
    }
  );
}

#[test]
fn single_input_rune_partial_sell_offer_that_fills() {
  let core = mockcore::builder().network(Network::Regtest).build();

  let ord = TestServer::spawn_with_server_args(&core, &["--index-runes", "--regtest"], &[]);

  create_wallet(&core, &ord);

  etch(&core, &ord, Rune(RUNE));

  let send = CommandBuilder::new(format!(
    "
      --chain regtest
      wallet
      send
      --fee-rate 1
      bcrt1qs758ursh4q9z627kt3pp5yysm78ddny6txaqgw 750:{}
    ",
    Rune(RUNE),
  ))
  .core(&core)
  .ord(&ord)
  .run_and_deserialize_output::<Send>();

  core.mine_blocks(1);

  let create = CommandBuilder::new(format!(
    "--regtest wallet sell-offer create --outgoing {}:{} --amount 1btc --allow-partial",
    250,
    Rune(RUNE),
  ))
  .core(&core)
  .ord(&ord)
  .run_and_deserialize_output::<Create>();

  assert_eq!(
    create.outgoing,
    Outgoing::Rune {
      rune: SpacedRune {
        rune: Rune(RUNE),
        spacers: 0,
      },
      decimal: "250".parse().unwrap(),
    }
  );

  assert_eq!(create.amount, Amount::from_sat(100_000_000));

  assert!(!create.has_multiple);
  assert!(!create.is_partial);

  let outputs = CommandBuilder::new("--regtest wallet outputs")
    .core(&core)
    .ord(&ord)
    .run_and_deserialize_output::<Vec<ord::subcommand::wallet::outputs::Output>>();

  let psbt = Psbt::deserialize(&base64_decode(&create.psbt).unwrap()).unwrap();

  assert_eq!(psbt.unsigned_tx.input.len(), 1);
  assert_eq!(psbt.unsigned_tx.output.len(), 1);

  assert!(outputs
    .iter()
    .any(|output| output.output == psbt.unsigned_tx.input[0].previous_output));

  assert!(core.state().is_wallet_address(
    &Address::from_script(&psbt.unsigned_tx.output[0].script_pubkey, Network::Regtest).unwrap()
  ));

  // verify input is signed with SINGLE|ANYONECANPAY
  assert_eq!(
    psbt.inputs[0].final_script_witness,
    Some(Witness::from_slice(&[&[1; 64]]))
  );

  pretty_assertions::assert_eq!(
    psbt.unsigned_tx,
    Transaction {
      version: Version(2),
      lock_time: LockTime::ZERO,
      input: vec![TxIn {
        previous_output: OutPoint {
          txid: send.txid,
          vout: 1,
        },
        script_sig: ScriptBuf::new(),
        sequence: Sequence::ENABLE_RBF_NO_LOCKTIME,
        witness: Witness::new(),
      }],
      output: vec![TxOut {
        value: Amount::from_sat(100_010_000),
        script_pubkey: psbt.unsigned_tx.output[0].script_pubkey.clone(),
      }],
    }
  );
}

#[test]
fn error_rune_must_exist() {
  let core = mockcore::builder().network(Network::Regtest).build();

  let ord = TestServer::spawn_with_server_args(&core, &["--index-runes", "--regtest"], &[]);

  create_wallet(&core, &ord);

  CommandBuilder::new("--regtest wallet sell-offer create --outgoing 1:FOO --amount 1btc")
    .core(&core)
    .ord(&ord)
    .expected_stderr("error: rune `FOO` has not been etched\n")
    .expected_exit_code(1)
    .run_and_extract_stdout();
}

#[test]
fn error_no_isolated_rune_balance_in_wallet() {
  let core = mockcore::builder().network(Network::Regtest).build();

  let ord = TestServer::spawn_with_server_args(&core, &["--index-runes", "--regtest"], &[]);

  create_wallet(&core, &ord);

  let rune0 = Rune(RUNE);
  let rune1 = Rune(RUNE + 1);
  let a = etch(&core, &ord, rune0);
  let b = etch(&core, &ord, rune1);

  let (block0, tx0) = core.tx_index(a.output.reveal);
  let (block1, tx1) = core.tx_index(b.output.reveal);

  core.mine_blocks(1);

  let address = core.state().new_address(false);

  core.broadcast_tx(TransactionTemplate {
    inputs: &[(block0, tx0, 1, default()), (block1, tx1, 1, default())],
    recipient: Some(address),
    ..default()
  });

  core.mine_blocks(1);

  CommandBuilder::new(format!(
    "--regtest wallet sell-offer create --outgoing 1000:{} --amount 1btc",
    Rune(RUNE),
  ))
  .core(&core)
  .ord(&ord)
  .expected_stderr(format!(
    "error: missing utxo in wallet with only a `{}` balance\n",
    Rune(RUNE),
  ))
  .expected_exit_code(1)
  .run_and_extract_stdout();
}

#[test]
fn error_inexact_rune_balance() {
  let core = mockcore::builder().network(Network::Regtest).build();

  let ord = TestServer::spawn_with_server_args(&core, &["--index-runes", "--regtest"], &[]);

  create_wallet(&core, &ord);

  etch(&core, &ord, Rune(RUNE));

  CommandBuilder::new(format!(
    "--regtest wallet sell-offer create --outgoing 2000:{} --amount 1btc",
    Rune(RUNE),
  ))
  .core(&core)
  .ord(&ord)
  .expected_stderr(format!(
    "error: missing utxo in wallet with exact `2000:{}` balance (try using --allow-partial)\n",
    Rune(RUNE),
  ))
  .expected_exit_code(1)
  .run_and_extract_stdout();
}

#[test]
fn error_multiple_utxos_required() {
  let core = mockcore::builder().network(Network::Regtest).build();

  let ord = TestServer::spawn_with_server_args(&core, &["--index-runes", "--regtest"], &[]);

  create_wallet(&core, &ord);

  batch(
    &core,
    &ord,
    batch::File {
      etching: Some(batch::Etching {
        divisibility: 0,
        rune: SpacedRune {
          rune: Rune(RUNE),
          spacers: 0,
        },
        premine: "0".parse().unwrap(),
        supply: "2000".parse().unwrap(),
        symbol: '¢',
        terms: Some(batch::Terms {
          cap: 2,
          offset: None,
          amount: "1000".parse().unwrap(),
          height: None,
        }),
        turbo: false,
      }),
      inscriptions: vec![batch::Entry {
        file: Some("inscription.jpeg".into()),
        ..default()
      }],
      ..default()
    },
  );

  CommandBuilder::new(format!(
    "--regtest wallet mint --fee-rate 1 --rune {}",
    Rune(RUNE)
  ))
  .core(&core)
  .ord(&ord)
  .run_and_deserialize_output::<ord::subcommand::wallet::mint::Output>();

  core.mine_blocks(1);

  CommandBuilder::new(format!(
    "--regtest wallet mint --fee-rate 1 --rune {}",
    Rune(RUNE)
  ))
  .core(&core)
  .ord(&ord)
  .run_and_deserialize_output::<ord::subcommand::wallet::mint::Output>();

  core.mine_blocks(1);

  CommandBuilder::new(format!(
    "--regtest wallet sell-offer create --outgoing 2000:{} --amount 1btc",
    Rune(RUNE),
  ))
  .core(&core)
  .ord(&ord)
  .expected_stderr(format!(
    "error: missing utxo in wallet with exact `2000:{}` balance, but an exact multi-utxo offer exists (hint: use --allow-multiple-utxos)\n",
    Rune(RUNE),
  ))
  .expected_exit_code(1)
  .run_and_extract_stdout();
}

#[test]
fn error_no_exact_set_of_multiple_utxos() {
  let core = mockcore::builder().network(Network::Regtest).build();

  let ord = TestServer::spawn_with_server_args(&core, &["--index-runes", "--regtest"], &[]);

  create_wallet(&core, &ord);

  batch(
    &core,
    &ord,
    batch::File {
      etching: Some(batch::Etching {
        divisibility: 0,
        rune: SpacedRune {
          rune: Rune(RUNE),
          spacers: 0,
        },
        premine: "0".parse().unwrap(),
        supply: "2000".parse().unwrap(),
        symbol: '¢',
        terms: Some(batch::Terms {
          cap: 2,
          offset: None,
          amount: "1000".parse().unwrap(),
          height: None,
        }),
        turbo: false,
      }),
      inscriptions: vec![batch::Entry {
        file: Some("inscription.jpeg".into()),
        ..default()
      }],
      ..default()
    },
  );

  CommandBuilder::new(format!(
    "--regtest wallet mint --fee-rate 1 --rune {}",
    Rune(RUNE)
  ))
  .core(&core)
  .ord(&ord)
  .run_and_deserialize_output::<ord::subcommand::wallet::mint::Output>();

  core.mine_blocks(1);

  CommandBuilder::new(format!(
    "--regtest wallet mint --fee-rate 1 --rune {}",
    Rune(RUNE)
  ))
  .core(&core)
  .ord(&ord)
  .run_and_deserialize_output::<ord::subcommand::wallet::mint::Output>();

  core.mine_blocks(1);

  CommandBuilder::new(format!(
    "--regtest wallet sell-offer create --outgoing 3000:{} --amount 1btc --allow-multiple-utxos",
    Rune(RUNE),
  ))
  .core(&core)
  .ord(&ord)
  .expected_stderr(format!(
    "error: missing set of utxos in wallet summing to exactly `3000:{}` (try using --allow-partial)\n",
    Rune(RUNE),
  ))
  .expected_exit_code(1)
  .run_and_extract_stdout();
}

#[test]
fn error_unable_to_create_partial() {
  let core = mockcore::builder().network(Network::Regtest).build();

  let ord = TestServer::spawn_with_server_args(&core, &["--index-runes", "--regtest"], &[]);

  create_wallet(&core, &ord);

  etch(&core, &ord, Rune(RUNE));

  CommandBuilder::new(format!(
    "--regtest wallet sell-offer create --outgoing 500:{} --amount 1btc --allow-partial",
    Rune(RUNE),
  ))
  .core(&core)
  .ord(&ord)
  .expected_stderr(format!(
    "error: missing utxo in wallet with balance below `500:{}`\n",
    Rune(RUNE),
  ))
  .expected_exit_code(1)
  .run_and_extract_stdout();
}

#[test]
fn inscription_sell_offer_is_correct() {
  let core = mockcore::spawn();

  let ord = TestServer::spawn_with_server_args(&core, &[], &[]);

  create_wallet(&core, &ord);

  let seller_postage = 9000;
  let (inscription, txid) = inscribe_with_options(&core, &ord, Some(seller_postage), 0);

  core.mine_blocks(1);

  let create = CommandBuilder::new(format!(
    "wallet sell-offer create --outgoing {inscription} --amount 1btc",
  ))
  .core(&core)
  .ord(&ord)
  .run_and_deserialize_output::<Create>();

  assert_eq!(create.outgoing, Outgoing::InscriptionId(inscription));

  assert_eq!(create.amount, Amount::from_sat(100_000_000));

  assert!(!create.has_multiple);
  assert!(!create.is_partial);

  let outputs = CommandBuilder::new("wallet outputs")
    .core(&core)
    .ord(&ord)
    .run_and_deserialize_output::<Vec<ord::subcommand::wallet::outputs::Output>>();

  let psbt = Psbt::deserialize(&base64_decode(&create.psbt).unwrap()).unwrap();

  assert_eq!(psbt.unsigned_tx.input.len(), 1);
  assert_eq!(psbt.unsigned_tx.output.len(), 1);

  assert!(outputs
    .iter()
    .any(|output| output.output == psbt.unsigned_tx.input[0].previous_output));

  assert!(core.state().is_wallet_address(
    &Address::from_script(&psbt.unsigned_tx.output[0].script_pubkey, Network::Bitcoin).unwrap()
  ));

  // verify input is signed with SINGLE|ANYONECANPAY
  assert_eq!(
    psbt.inputs[0].final_script_witness,
    Some(Witness::from_slice(&[&[1; 64]]))
  );

  pretty_assertions::assert_eq!(
    psbt.unsigned_tx,
    Transaction {
      version: Version(2),
      lock_time: LockTime::ZERO,
      input: vec![TxIn {
        previous_output: OutPoint { txid, vout: 0 },
        script_sig: ScriptBuf::new(),
        sequence: Sequence::ENABLE_RBF_NO_LOCKTIME,
        witness: Witness::new(),
      }],
      output: vec![TxOut {
        value: Amount::from_sat(100_009_000),
        script_pubkey: psbt.unsigned_tx.output[0].script_pubkey.clone(),
      }],
    }
  );
}

#[test]
fn error_inscription_not_in_wallet() {
  let core = mockcore::builder().network(Network::Regtest).build();

  let ord = TestServer::spawn_with_server_args(&core, &["--index-runes", "--regtest"], &[]);

  create_wallet(&core, &ord);

  CommandBuilder::new(
    "--regtest wallet sell-offer create --outgoing 6fb976ab49dcec017f1e201e84395983204ae1a7c2abf7ced0a85d692e442799i0 --amount 1btc"
  )
  .core(&core)
  .ord(&ord)
  .expected_stderr("error: inscription 6fb976ab49dcec017f1e201e84395983204ae1a7c2abf7ced0a85d692e442799i0 not in wallet\n")
  .expected_exit_code(1)
  .run_and_extract_stdout();
}
