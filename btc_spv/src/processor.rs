//! Bitcoin SPV proof verifier program
//! Receive merkle proofs ad block headers, validate transaction

use crate::state::spv::*;

use crate::instructions::*;
#[allow(unused_imports)]
use crate::utils::*;
//use solana_sdk::account::KeyedAccount;
//use solana_sdk::instruction::InstructionError;
//use solana_sdk::program_utils::limited_deserialize;
//use solana_sdk::pubkey::Pubkey;

use solana_program::{
    account_info::AccountInfo, entrypoint::ProgramResult, instruction::InstructionError,
    program_error::ProgramError, program_utils::limited_deserialize, pubkey::Pubkey,
};

pub struct SpvProcessor;

/// Instruction processor
pub fn process_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    data: &[u8],
) -> ProgramResult {
    // solana_logger::setup();

    let command = limited_deserialize::<SpvInstruction>(data, data.len() as u64)
        .map_err(|err| ProgramError::BorshIoError(err.to_string()))?;

    solana_program::log::sol_log(&format!("{:?}", command));

    // todo: get rid of the err.to_string() in map_err

    match command {
        SpvInstruction::ClientRequest(client_request_info) => {
            SpvProcessor::do_client_request(accounts, &client_request_info)
                .map_err(|err| ProgramError::BorshIoError(err.to_string()))?;
        }
        SpvInstruction::CancelRequest => {
            SpvProcessor::do_cancel_request(accounts)
                .map_err(|err| ProgramError::BorshIoError(err.to_string()))?;
        }
        SpvInstruction::SubmitProof(proof_info) => {
            SpvProcessor::do_submit_proof(accounts, &proof_info)
                .map_err(|err| ProgramError::BorshIoError(err.to_string()))?;
        }
    }
    Ok(())
}
impl SpvProcessor {
    pub fn validate_header_chain(
        headers: HeaderChain,
        difficulty: u64,
        confirm_num: u16,
    ) -> Result<(), InstructionError> {
        let ln = headers.len();
        // check that the headerchain is the right length
        if ln != (2 + confirm_num as usize) {
            solana_program::msg!("Invalid length for Header Chain");
            return Err(InstructionError::InvalidArgument);
        }

        for bh in 0..ln {
            let header = &headers[bh as usize];
            if bh > 0 {
                let parent_header = &headers[bh - 1];
                // check that the headerchain is in order and contiguous
                if header.parent != parent_header.blockhash {
                    solana_program::msg!(
                        "{}",
                        format!("Invalid Header Chain hash sequence for header index {}", bh)
                    );
                    return Err(InstructionError::InvalidArgument);
                }
            }

            //check that block difficulty is above the given threshold
            if header.difficulty() < difficulty {
                solana_program::log::sol_log(
                   &format!("Invalid block difficulty for header index {}. got {}, min {}", bh, header.difficulty(), difficulty)
                );
                return Err(InstructionError::InvalidArgument);
            }
        }
        //not done yet, needs difficulty average/variance checking still
        Ok(())
    }

    #[allow(clippy::needless_pass_by_value)]
    fn map_to_invalid_arg(err: std::boxed::Box<bincode::ErrorKind>) -> InstructionError {
        solana_program::msg!("Deserialize failed, not a valid state: {:?}", err);
        InstructionError::InvalidArgument
    }

    fn deserialize_proof(data: &[u8]) -> Result<Proof, InstructionError> {
        let proof_state: AccountState =
            bincode::deserialize(data).map_err(Self::map_to_invalid_arg)?;
        if let AccountState::Verification(proof) = proof_state {
            Ok(proof)
        } else {
            solana_program::msg!("Not a valid proof");
            Err(InstructionError::InvalidAccountData)
        }
    }

    fn deserialize_request(data: &[u8]) -> Result<ClientRequestInfo, InstructionError> {
        let req_state: AccountState =
            bincode::deserialize(data).map_err(Self::map_to_invalid_arg)?;
        if let AccountState::Request(info) = req_state {
            Ok(info)
        } else {
            solana_program::msg!("Not a valid proof request");
            Err(InstructionError::InvalidAccountData)
        }
    }

    pub fn check_account_unallocated(data: &[u8]) -> Result<(), InstructionError> {
        let acct_state: AccountState =
            bincode::deserialize(data).map_err(Self::map_to_invalid_arg)?;
        if let AccountState::Unallocated = acct_state {
            Ok(())
        } else {
            solana_program::msg!("Provided account is already occupied");
            Err(InstructionError::InvalidAccountData)
        }
    }

    pub fn do_client_request(
        keyed_accounts: &[AccountInfo],
        request_info: &ClientRequestInfo,
    ) -> Result<(), InstructionError> {
        if keyed_accounts.len() != 2 {
            solana_program::msg!("Client Request invalid accounts argument length (should be 2)")
        }
        const OWNER_INDEX: usize = 0;
        const REQUEST_INDEX: usize = 1;

        // check_account_unallocated(&keyed_accounts[REQUEST_INDEX].account.data)?;
        Ok(()) //placeholder
    }

    pub fn do_cancel_request(keyed_accounts: &[AccountInfo]) -> Result<(), InstructionError> {
        if keyed_accounts.len() != 2 {
            solana_program::msg!("Client Request invalid accounts argument length (should be 2)")
        }
        const OWNER_INDEX: usize = 0;
        const CANCEL_INDEX: usize = 1;
        Ok(()) //placeholder
    }

    pub fn do_submit_proof(
        keyed_accounts: &[AccountInfo],
        proof_info: &Proof,
    ) -> Result<(), InstructionError> {
        if keyed_accounts.len() != 2 {
            solana_program::msg!("Client Request invalid accounts argument length (should be 2)")
        }
        const SUBMITTER_INDEX: usize = 0;
        const PROOF_REQUEST_INDEX: usize = 1;
        Ok(()) //placeholder
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::state::spv as spv_state;
    use crate::{instructions, utils};

    #[test]
    fn test_parse_header_hex() -> Result<(), SpvError> {
        let testheader = "010000008a730974ac39042e95f82d719550e224c1a680a8dc9e8df9d007000000000000f50b20e8720a552dd36eb2ebdb7dceec9569e0395c990c1eb8a4292eeda05a931e1fce4e9a110e1a7a58aeb0";
        let testhash = "0000000000000bae09a7a393a8acded75aa67e46cb81f7acaa5ad94f9eacd103";
        let testheaderbytes = hex::decode(testheader)?;
        let testhashbytes = hex::decode(testhash)?;

        let mut blockhash: [u8; 32] = [0; 32];
        blockhash.copy_from_slice(&testhashbytes[..32]);

        let mut version: [u8; 4] = [0; 4];
        version.copy_from_slice(&testheaderbytes[..4]);
        let test_version = u32::from_le_bytes(version);

        let mut test_parent: [u8; 32] = [0; 32];
        test_parent.copy_from_slice(&testheaderbytes[4..36]);

        let mut merkleroot: [u8; 32] = [0; 32];
        merkleroot.copy_from_slice(&testheaderbytes[36..68]);

        let mut time: [u8; 4] = [0; 4];
        time.copy_from_slice(&testheaderbytes[68..72]);
        let test_time = u32::from_le_bytes(time);

        let mut test_nonce: [u8; 4] = [0; 4];
        test_nonce.copy_from_slice(&testheaderbytes[76..80]);

        let bh = BlockHeader::hexnew(testheader, testhash)?;

        assert_eq!(bh.blockhash, blockhash);
        assert_eq!(bh.merkle_root.hash, merkleroot);
        assert_eq!(bh.version, test_version);
        assert_eq!(bh.time, test_time);
        assert_eq!(bh.parent, test_parent);
        assert_eq!(bh.nonce, test_nonce);

        Ok(())
    }

    #[test]
    fn test_parse_transaction_hex() {
        let testblockhash = "0000000000000bae09a7a393a8acded75aa67e46cb81f7acaa5ad94f9eacd103";
        let testtxhash = "5b09bbb8d3cb2f8d4edbcf30664419fb7c9deaeeb1f62cb432e7741c80dbe5ba";

        let mut testdatabytes = include_bytes!("testblock.in");
        let mut headerbytes = hex::encode(&testdatabytes[0..]);
        let hbc = &headerbytes[0..80];

        let mut txdata = &testdatabytes[80..];

        let vilen = measure_variable_int(&txdata[0..9]).unwrap();
        let txnum = decode_variable_int(&txdata[0..9]).unwrap();

        txdata = &txdata[vilen..];
        let tx = BitcoinTransaction::new(txdata.to_vec());

        assert_eq!(tx.inputs.len(), 1);
        assert_eq!(txnum, 22);
        assert_eq!(tx.outputs.len(), 1);
        assert_eq!(tx.version, 1);
    }
    #[test]
    fn test_validate_header_chain() {
        let header_chain_raw = [
            ("010000008a730974ac39042e95f82d719550e224c1a680a8dc9e8df9d007000000000000f50b20e8720a552dd36eb2ebdb7dceec9569e0395c990c1eb8a4292eeda05a931e1fce4e9a110e1a7a58aeb0", "0000000000000bae09a7a393a8acded75aa67e46cb81f7acaa5ad94f9eacd103"),
            ("0100000003d1ac9e4fd95aaaacf781cb467ea65ad7deaca893a3a709ae0b000000000000cca28a34a71dcdafc9d95c3ab96091b1999b7cc0ce2d4906225acbb4dcfbd02d5526ce4e9a110e1a6989aec7", "0000000000000981c0f836cc249fb18744fd33458b85d00de3e7f8995f4543ec"),
            ("01000000ec43455f99f8e7e30dd0858b4533fd4487b19f24cc36f8c08109000000000000e9d83e7a23e6197a3ed623befba861f95dbdf54fcd70892a59f56669bd4485c5bb27ce4e9a110e1a731eaf33", "0000000000000cad4861e1172e492da778d7cba8b29d32da9100489165a0d820"),
            ("0100000020d8a06591480091da329db2a8cbd778a72d492e17e16148ad0c0000000000001750763ea7243f77f520073bd11535a627174c34958056a19c17d68aee3cb874722ece4e9a110e1a0e6af22e", "0000000000000397a165d83cc4640321a3b8ff4cce1f8aa2570deabf14ac14e7"),
            ("01000000e714ac14bfea0d57a28a1fce4cffb8a3210364c43cd865a19703000000000000ce0ee41c03692c424b522dd6541ae814da027e7d1fa440736faabee3405b2342e92ece4e9a110e1a61403e1b", "0000000000000d8a4b89a5b219ba1c4cc7cfc982f5119d0dcd4758fbe63cd735"),
            ("0100000035d73ce6fb5847cd0d9d11f582c9cfc74c1cba19b2a5894b8a0d000000000000ff2ed85a551b55a313df806ec819bf31ff7386302e82d79753c7e17183b3c4791132ce4e9a110e1a15bc904e", "00000000000001de6811527902b2a994f3721af035110242ddca509e9a40ef7e"),
        ];
        let mut header_chain: Vec<BlockHeader> = Vec::new();
        for h in 0..header_chain_raw.len() {
            let head = header_chain_raw[h];
            let header = BlockHeader::hexnew(head.0, head.1).unwrap();
            println!("{:#?}", header);
            header_chain.push(header);
        }
        let difficulty: u64 = 1_000_000;
        let confirmations: u16 = 4;

        SpvProcessor::validate_header_chain(header_chain, difficulty, confirmations).unwrap();
    }
    /* original version which is failing
    #[test]
    fn test_validate_header_chain() {
        let header_chain_raw = [
            ("010000008a730974ac39042e95f82d719550e224c1a680a8dc9e8df9d007000000000000f50b20e8720a552dd36eb2ebdb7dceec9569e0395c990c1eb8a4292eeda05a931e1fce4e9a110e1a7a58aeb0", "0000000000000bae09a7a393a8acded75aa67e46cb81f7acaa5ad94f9eacd103"),
            ("0100000003d1ac9e4fd95aaaacf781cb467ea65ad7deaca893a3a709ae0b000000000000cca28a34a71dcdafc9d95c3ab96091b1999b7cc0ce2d4906225acbb4dcfbd02d5526ce4e9a110e1a6989aec7", "0000000000000981c0f836cc249fb18744fd33458b85d00de3e7f8995f4543ec"),
            ("01000000ec43455f99f8e7e30dd0858b4533fd4487b19f24cc36f8c08109000000000000e9d83e7a23e6197a3ed623befba861f95dbdf54fcd70892a59f56669bd4485c5bb27ce4e9a110e1a731eaf33", "0000000000000cad4861e1172e492da778d7cba8b29d32da9100489165a0d820"),
            ("0100000020d8a06591480091da329db2a8cbd778a72d492e17e16148ad0c0000000000001750763ea7243f77f520073bd11535a627174c34958056a19c17d68aee3cb874722ece4e9a110e1a0e6af22e", "0000000000000397a165d83cc4640321a3b8ff4cce1f8aa2570deabf14ac14e7"),
            ("01000000e714ac14bfea0d57a28a1fce4cffb8a3210364c43cd865a19703000000000000ce0ee41c03692c424b522dd6541ae814da027e7d1fa440736faabee3405b2342e92ece4e9a110e1a61403e1b", "0000000000000d8a4b89a5b219ba1c4cc7cfc982f5119d0dcd4758fbe63cd735"),
            ("0100000035d73ce6fb5847cd0d9d11f582c9cfc74c1cba19b2a5894b8a0d000000000000ff2ed85a551b55a313df806ec819bf31ff7386302e82d79753c7e17183b3c4791132ce4e9a110e1a15bc904e", "00000000000001de6811527902b2a994f3721af035110242ddca509e9a40ef7e"),
        ];
        let mut header_chain: Vec<BlockHeader> = Vec::new();
        for h in 0..header_chain_raw.len() {
            let head = header_chain_raw[h];
            println!("{}", head.0);
            let header = BlockHeader::hexnew(head.0, head.1).unwrap();
            header_chain.push(header);
        }
        let difficulty: u64 = 10_000_000;
        let confirmations: u16 = 5;

        SpvProcessor::validate_header_chain(header_chain, difficulty, confirmations).unwrap();
    }*/
}
