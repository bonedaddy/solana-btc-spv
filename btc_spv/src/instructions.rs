//! Spv proof Verification Program
use crate::state::spv::*;
use crate::ID as id;
use serde::{Deserialize, Serialize};
use solana_program::{
    instruction::{AccountMeta, Instruction},
    pubkey::Pubkey,
};

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone)]
pub enum SpvInstruction {
    // Client Places request for a matching proof
    // key 0 - Signer
    // key 1 - Account in which to record the Request and proof
    ClientRequest(ClientRequestInfo),

    // Used by clients to cancel a pending proof request
    // key 0 - signer
    // key 1 - Request to cancel
    CancelRequest,

    // used to submit a proof matching a posted BitcoinTxHash or for own benefit
    // key 0 - signer
    // key 1 - Request to prove
    SubmitProof(Proof),
}

pub fn client_request(
    owner: &Pubkey,
    txhash: BitcoinTxHash,
    fee: u64,
    confirmations: u8,
    difficulty: u64,
    expiration: Option<u32>,
) -> Instruction {
    let account_meta = vec![AccountMeta::new(*owner, true)];
    Instruction::new(
        id,
        &SpvInstruction::ClientRequest(ClientRequestInfo {
            txhash,
            confirmations,
            fee,
            difficulty,
            expiration,
        }),
        account_meta,
    )
}

pub fn cancel_request(owner: &Pubkey, request: &Pubkey) -> Instruction {
    let account_meta = vec![
        AccountMeta::new(*owner, true),
        AccountMeta::new(*request, false),
    ];
    Instruction::new(id, &SpvInstruction::CancelRequest, account_meta)
}

pub fn submit_proof(
    submitter: &Pubkey,
    proof: MerkleProof,
    headers: HeaderChain,
    transaction: BitcoinTransaction,
    request: &Pubkey,
) -> Instruction {
    let account_meta = vec![
        AccountMeta::new(*submitter, true),
        AccountMeta::new(*request, false),
    ];
    Instruction::new(
        id,
        &SpvInstruction::SubmitProof(Proof {
            submitter: *submitter,
            proof,
            headers,
            transaction,
            request: *request,
        }),
        account_meta,
    )
}
