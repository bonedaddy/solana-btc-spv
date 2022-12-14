#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unused_mut)]
#![allow(dead_code)]
// This version is a work in progress and contains placeholders and incomplete components
pub mod instructions;
pub mod processor;
pub mod utils;
pub mod state;

mod entrypoint;

use solana_program::pubkey::Pubkey;
use crate::processor::process_instruction;

pub const ID: Pubkey = solana_program::pubkey!("3VsEWnjL2Q6rp1Do2X1xH7g81HDWmFDZn8UZJWrsK4Nk");
