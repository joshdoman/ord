use {
  super::*,
  serde_hex::{SerHex, Strict},
};

pub use crate::{
  subcommand::decode::Output as Decode,
  templates::{
    BlocksHtml as Blocks, RuneHtml as Rune, RunesHtml as Runes, StatusHtml as Status,
    TransactionHtml as Transaction,
  },
};

#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct Block {
  pub best_height: u32,
  pub hash: BlockHash,
  pub height: u32,
  pub runes: Vec<SpacedRune>,
  pub target: BlockHash,
  pub transactions: Vec<bitcoin::blockdata::transaction::Transaction>,
}

impl Block {
  pub(crate) fn new(
    block: bitcoin::Block,
    height: Height,
    best_height: Height,
    runes: Vec<SpacedRune>,
  ) -> Self {
    Self {
      hash: block.header.block_hash(),
      target: target_as_block_hash(block.header.target()),
      height: height.0,
      best_height: best_height.0,
      runes,
      transactions: block.txdata,
    }
  }
}

#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct BlockInfo {
  pub average_fee: u64,
  pub average_fee_rate: u64,
  pub bits: u32,
  #[serde(with = "SerHex::<Strict>")]
  pub chainwork: [u8; 32],
  pub confirmations: i32,
  pub difficulty: f64,
  pub hash: BlockHash,
  pub feerate_percentiles: [u64; 5],
  pub height: u32,
  pub max_fee: u64,
  pub max_fee_rate: u64,
  pub max_tx_size: u32,
  pub median_fee: u64,
  pub median_time: Option<u64>,
  pub merkle_root: TxMerkleNode,
  pub min_fee: u64,
  pub min_fee_rate: u64,
  pub next_block: Option<BlockHash>,
  pub nonce: u32,
  pub previous_block: Option<BlockHash>,
  pub subsidy: u64,
  pub target: BlockHash,
  pub timestamp: u64,
  pub total_fee: u64,
  pub total_size: usize,
  pub total_weight: usize,
  pub transaction_count: u64,
  pub version: u32,
}

#[derive(Debug, PartialEq, Serialize, Deserialize, Copy, Clone)]
pub struct SupplyState {
  pub supply0: u128,
  pub supply1: u128,
  pub burned0: u128,
  pub burned1: u128,
}

#[derive(Debug, PartialEq, Serialize, Deserialize, Copy, Clone)]
pub struct UtilState {
  pub bonds_per_sat: u128,
  pub utils_per_bond: u128,
  pub utils_per_sat: u128,
  pub interest_rate: u128,
  pub decimals: u128,
}

#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct RateHistory {
  pub median_interest_rate: u128,
  pub history: Vec<u128>,
}

#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct Output {
  pub address: Option<Address<NetworkUnchecked>>,
  pub indexed: bool,
  pub inscriptions: Vec<InscriptionId>,
  pub runes: BTreeMap<SpacedRune, Pile>,
  pub sat_ranges: Option<Vec<(u64, u64)>>,
  pub script_pubkey: String,
  pub spent: bool,
  pub transaction: String,
  pub value: u64,
}

impl Output {
  pub fn new(
    chain: Chain,
    inscriptions: Vec<InscriptionId>,
    outpoint: OutPoint,
    tx_out: TxOut,
    indexed: bool,
    runes: BTreeMap<SpacedRune, Pile>,
    sat_ranges: Option<Vec<(u64, u64)>>,
    spent: bool,
  ) -> Self {
    Self {
      address: chain
        .address_from_script(&tx_out.script_pubkey)
        .ok()
        .map(|address| uncheck(&address)),
      indexed,
      inscriptions,
      runes,
      sat_ranges,
      script_pubkey: tx_out.script_pubkey.to_asm_string(),
      spent,
      transaction: outpoint.txid.to_string(),
      value: tx_out.value,
    }
  }
}

#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct Sat {
  pub block: u32,
  pub charms: Vec<Charm>,
  pub cycle: u32,
  pub decimal: String,
  pub degree: String,
  pub epoch: u32,
  pub inscriptions: Vec<InscriptionId>,
  pub name: String,
  pub number: u64,
  pub offset: u64,
  pub percentile: String,
  pub period: u32,
  pub rarity: Rarity,
  pub satpoint: Option<SatPoint>,
  pub timestamp: i64,
}
