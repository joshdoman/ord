use super::*;

pub mod accept;
pub mod create;

#[derive(Debug, Parser)]
pub(crate) enum BuyOffer {
  #[command(about = "Accept offer to buy inscription or rune")]
  Accept(accept::Accept),
  #[command(about = "Create offer to buy inscription or rune")]
  Create(create::Create),
}

impl BuyOffer {
  pub(crate) fn run(self, wallet: Wallet) -> SubcommandResult {
    match self {
      Self::Accept(accept) => accept.run(wallet),
      Self::Create(create) => create.run(wallet),
    }
  }
}
