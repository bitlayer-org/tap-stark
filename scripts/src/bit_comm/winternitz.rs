//
// License Claim: This file is optimized based https://github.com/BitVM/BitVM/blob/main/src/signatures/winternitz.rs
//

// Winternitz One-time Signatures
//
// Winternitz signatures are an improved version of Lamport signatures.
// A detailed introduction to Winternitz signatures can be found
// in "A Graduate Course in Applied Cryptography" in chapter 14.3
// https://toc.cryptobook.us/book.pdf
//
// We are trying to closely follow the authors' notation here.
//

//
// BEAT OUR IMPLEMENTATION AND WIN A CODE GOLF BOUNTY!
//

pub use bitcoin_script::{define_pushable, script};
use serde::{Deserialize, Serialize};

pub use crate::execute_script;

define_pushable!();
use bitcoin::hashes::{hash160, Hash};
use bitcoin::ScriptBuf as Script;
use hex::decode as hex_decode;
// 0000 ~ 1111 (0~15)

// vcalue  0001  0010  0011  0100
// secret   A     B     C     D
// maxCheckum = 15 x 4 = 60  need 6bit
// checksum = 1 + 2 +3 +4 = 10  (has 6 preimage)
// pubkey    = Hash_256(A) HASH_256(B) HASH_256(C) HASH_256(D)
// signature = Hash_1(A)  Hash_2(B)    Hash_3(C)   Hash_4(D)    checksum = {nil nil preiamge nil preimage nil }
// verify :
//    HASH_255(HASH_1(A)) ==  Hash_256(A) HASH_254(HASH_2(B)) == HASH_256(B) HASH_253(HASH_3(C)) == HASH_256(C) HASH_252(HASH_4(D)) == HASH_256(D)
//    reveal preiamge for checksum and must to equal to 10

/// Bits per digit
pub const LOG_D: u32 = 4;
pub const LOG_D_USIZE: usize = 4;
/// Digits are base d+1
pub const DIGITS: u32 = (1 << LOG_D) - 1;
/// Number of digits of the message (8x15=120 checksum need 7bits(2 digits))
pub const N0_INS: usize = 8;
/// Number of digits of the checksum
pub const N1_INS: usize = 2;
/// Total number of digits to be signed
pub const N_INS: usize = N0_INS + N1_INS;

pub const N: usize = 10;
pub const N0: usize = 8;
pub const N1: usize = 2;
//
// Helper functions
//
#[derive(Serialize, Deserialize, Default, Debug, Clone, PartialEq, Eq)]
pub struct Winternitz {
    secret_key: String,
    pub_key: Vec<Vec<u8>>,
}

impl Winternitz {
    pub fn new(secret_key: &str) -> Self {
        let mut pubkey = Vec::new();

        for i in 0..N {
            pubkey.push(generate_public_key(&secret_key, i as u32));
        }

        Self {
            secret_key: String::from(secret_key),
            pub_key: pubkey,
        }
    }

    /// Generate the public key for the i-th digit of the message
    pub fn public_key(&self, digit_index: u32) -> &Vec<u8> {
        &self.pub_key[digit_index as usize]
    }

    pub fn pub_key(&self) -> &Vec<Vec<u8>> {
        &self.pub_key
    }

    pub fn public_key_script(&self, digit_index: u32) -> Script {
        let hash_bytes = self.public_key(digit_index).clone();

        script! {
            { hash_bytes }
        }
    }

    /// Compute the signature for the i-th digit of the message
    pub fn digit_signature(&self, digit_index: u32, message_digit: u8) -> (Vec<u8>, u8) {
        // Convert secret_key from hex string to bytes
        let mut secret_i = match hex_decode(&self.secret_key) {
            Ok(bytes) => bytes,
            Err(_) => panic!("Invalid hex string"),
        };

        secret_i.push(digit_index as u8);

        let mut hash = hash160::Hash::hash(&secret_i);

        for _ in 0..message_digit {
            hash = hash160::Hash::hash(&hash[..]);
        }

        let hash_bytes = hash.as_byte_array().to_vec();

        (hash_bytes, message_digit)
    }

    /// Compute the signature for the i-th digit of the message
    pub fn digit_signature_script(&self, digit_index: u32, message_digit: u8) -> Script {
        // Convert secret_key from hex string to bytes
        let (hash_bytes, message_digit) = self.digit_signature(digit_index, message_digit);

        script! {
            { hash_bytes }
            { message_digit }
        }
    }

    /// Compute the checksum of the message's digits.
    /// Further infos in chapter "A domination free function for Winternitz signatures"
    pub fn checksum(&self, digits: &[u8]) -> u32 {
        assert_eq!(digits.len(), N0);
        let mut sum = 0;
        for digit in digits {
            sum += *digit as u32;
        }
        DIGITS * N0 as u32 - sum
    }

    /// Compute the signature for a given message
    pub fn sign(&self, message_digits: &[u8]) -> Vec<Vec<u8>> {
        // if the message is [1, 2, 3, 4, 5, 6, 7, 8]; checksum=36 120-36=84(0101,0100)[5,4]
        // but the checksum_digits here has been reverse into [4,5]
        let mut checksum_digits = to_digits(self.checksum(message_digits), N1);
        checksum_digits.append(&mut message_digits.to_vec());

        let mut signature: Vec<Vec<u8>> = Vec::new();
        for i in 0..N {
            let (hash, digit) =
                self.digit_signature(i as u32, checksum_digits[(N - 1 - i) as usize]);
            signature.push(hash); // The reason why reverse order is used here is because it needs to be pushed onto the stack
            signature.push(vec![digit]);
        }
        assert!(signature.len() == 2 * N as usize);
        signature
    }

    /// Compute the signature for a given message
    pub fn sign_script(&self, message_digits: &[u8]) -> Script {
        // const message_digits = to_digits(message, n0)
        let mut checksum_digits = to_digits(self.checksum(message_digits), N1);
        checksum_digits.append(&mut message_digits.to_vec());

        script! {

            for i in 0..N {
                // the checksum must be N-1-i(can not set i reason) because we must ensure that the checkum only can modify to a smallet number when the digit only can modify to a bigger number by a malious part.
                { self.digit_signature_script( i as u32, checksum_digits[ (N-1-i) as usize]) }
            }
        }
    }

    pub fn checksig_verify(&self, pub_key: &[Vec<u8>]) -> Script {
        // If the mssage splits as  [A,B,C,D] [checkum_digit1,checksum_digit2]
        // The following input signature looks like:
        // {A_sig Hash}, {A digit}, {A_sig Hash}, {B digit}, {B_sig Hash}, {C digit}, {C_sig Hash}, {D digit}, {D_sig Hash},
        // ===  STACK  ====
        // |  A_digit   |
        // | A_sig HASH |
        // |  B_digit   |
        // | B_sig HASH |
        // |     ...    | ..N
        // |  checkum_digit1|
        // |  C1_HASH   |
        // |  checkum_digit2|
        // |  C2_HASH   | ..N1
        script! {
            //
            // Verify the hash chain for each digit
            //

            // Repeat this for every of the n many digits
            for digit_index in 0..N {
                // Verify that the digit is in the range [0, d]
                // See https://github.com/BitVM/BitVM/issues/35
                { DIGITS }
                OP_MIN // Return the smaller number

                // Push two copies of the digit onto the altstack
                OP_DUP
                OP_TOALTSTACK
                OP_TOALTSTACK

                // Hash the input hash d times and put every result on the stack
                for _ in 0..DIGITS {
                    OP_DUP OP_HASH160
                }

                // Verify the signature for this digit
                OP_FROMALTSTACK
                OP_PICK
                { pub_key[(N - 1 - digit_index) as usize].clone() }
                OP_EQUALVERIFY

                // Drop the d+1 stack items
                for _ in 0..(DIGITS+1)/2 {
                    OP_2DROP
                }
            }


            //
            // Verify the Checksum
            //

            // 1. Compute the checksum of the message's digits
            OP_FROMALTSTACK OP_DUP OP_NEGATE
            for _ in 1..N0 {
                OP_FROMALTSTACK OP_TUCK OP_SUB
            }
            { DIGITS * N0 as u32 }
            OP_ADD


            // 2. Sum up the signed checksum's digits
            OP_FROMALTSTACK
            for _ in 0..N1 - 1 {
                for _ in 0..LOG_D {
                    OP_DUP OP_ADD
                }
                OP_FROMALTSTACK
                OP_ADD
            }

            // 3. Ensure both checksums are equal
            OP_EQUALVERIFY


            // Convert the message's digits to bytes
            for i in 0..N0 / 2 {
                OP_SWAP
                for _ in 0..LOG_D {
                    OP_DUP OP_ADD
                }
                OP_ADD
                // Push all bytes to the altstack, except for the last byte
                if i != (N0/2) - 1 {
                    OP_TOALTSTACK
                }
            }
            // Read the bytes from the altstack
            for _ in 0..N0 / 2 - 1{
                OP_FROMALTSTACK
            }

        }
    }
    pub fn checksig_verify_self_pubkey(&self) -> Script {
        self.checksig_verify(&self.pub_key().as_slice())
    }
}
/// Generate the public key for the i-th digit of the message
pub fn generate_public_key(secret_key: &str, digit_index: u32) -> Vec<u8> {
    // Convert secret_key from hex string to bytes
    let mut secret_i = match hex_decode(secret_key) {
        Ok(bytes) => bytes,
        Err(_) => panic!("Invalid hex string"),
    };

    secret_i.push(digit_index as u8);

    let mut hash = hash160::Hash::hash(&secret_i);

    for _ in 0..DIGITS {
        hash = hash160::Hash::hash(&hash[..]);
    }

    hash.as_byte_array().to_vec()
}

/// Convert a number to digits
pub fn to_digits(mut number: u32, digit_count: usize) -> Vec<u8> {
    let mut digits = vec![0u8; digit_count];
    for i in 0..digit_count {
        let digit = number % (DIGITS + 1);
        number = (number - digit) / (DIGITS + 1);
        digits[i] = digit as u8;
    }
    digits
}

// The equivocation script is anyone can prove that the prover reveal two valid signatures
// The input of this function is two signatures and the script uses to check these signatures whether all valid.
// So we need to force these two signature is different
pub fn equivocation(_pub_key: &[Vec<u8>]) -> Script {
    script! {}
}

#[cfg(test)]
mod test {

    use p3_baby_bear::BabyBear;

    use super::*;
    use crate::execute_script_with_inputs;

    // The secret key
    const MY_SECKEY: &str = "b138982ce17ac813d505b5b40b665d404e9528e7"; // 20 byte

    #[test]
    fn test_checksum() {
        let winter = Winternitz::new("1234");
        let message_digits: [u8; N0_INS as usize] = [1, 2, 3, 4, 5, 6, 7, 8];
        // if the message is [1, 2, 3, 4, 5, 6, 7, 8]; checksum=36 120-36=84(0101,0100)[5,4]
        let sum = winter.checksum(&message_digits);
        assert_eq!(sum, 84);
        let checksum_digits = to_digits(winter.checksum(&message_digits), N1).to_vec();
        assert_eq!(checksum_digits, vec![4, 5]);
    }

    #[test]
    fn test_winternitz() {
        // the origin value is [1000,0111,0110,0101,0100,0011,0010,0001]
        // for the u8 resprentation [0x87,0x65,0x43,0x21]
        let winter = Winternitz::new("1234");
        let origin_value: u32 = 0x87654321;
        // let message = winter.to_digits(origin_value);
        let message = to_digits(origin_value, N0);
        const MESSAGE: [u8; N0_INS as usize] = [1, 2, 3, 4, 5, 6, 7, 8];
        assert_eq!(message, MESSAGE);

        let mut pubkey = Vec::new();
        for i in 0..N_INS {
            pubkey.push(winter.public_key(i as u32).clone());
        }

        let script = script! {
            { winter.sign_script(& MESSAGE) } // digit 0 = [checkum hash_i]
            { winter.checksig_verify(pubkey.as_slice()) }// using secret key to generate pubkey

            0x21 OP_EQUALVERIFY
            0x43 OP_EQUALVERIFY
            0x65 OP_EQUALVERIFY
            0x87 OP_EQUAL
        };

        println!(
            "Winternitz signature size: {:?} bytes per 80 bits",
            script.as_bytes().len()
        );
        let exec_result = execute_script(script);
        assert!(exec_result.success);

        // test zero case
        let origin_value: u32 = 0xED65002F;
        let message = to_digits(origin_value, N0);
        const MESSAGE_1: [u8; N0_INS as usize] = [0xF, 2, 0, 0, 5, 6, 0xD, 0xE];
        assert_eq!(message, MESSAGE_1);

        let script = script! {
            { winter.sign_script(& MESSAGE_1) } // digit 0 = [checkum hash_i]
            { winter.checksig_verify(winter.pub_key.as_slice()) }// using secret key to generate pubkey

            0x2F OP_EQUALVERIFY
            0x00 OP_EQUALVERIFY
            0x65 OP_EQUALVERIFY
            0xED OP_EQUALVERIFY
            OP_1
        };

        println!(
            "Winternitz signature size: {:?} bytes per 80 bits",
            script.as_bytes().len()
        );
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    #[test]
    fn test_winternitz_with_input() {
        // ======== Test 1...F CASE ============
        let winter = Winternitz::new("1234");

        const MESSAGE: [u8; N0_INS as usize] = [1, 2, 3, 4, 5, 6, 7, 8];

        let mut pubkey = Vec::new();
        for i in 0..N_INS {
            pubkey.push(winter.public_key(i as u32));
        }

        let script = script! {
            { winter.checksig_verify(winter.pub_key().as_slice()) }// using secret key to generate pubkey

            0x21 OP_EQUALVERIFY
            0x43 OP_EQUALVERIFY
            0x65 OP_EQUALVERIFY
            0x87 OP_EQUALVERIFY
            OP_1
        };

        println!(
            "Winternitz signature size: {:?} bytes per 80 bits",
            script.as_bytes().len()
        );

        let sig0 = winter.sign(&MESSAGE);
        let exec_result = execute_script_with_inputs(script, sig0.clone());
        assert!(exec_result.success);

        // Test 0xA 0xB 0xC 0xD 0xE 0xF Case
        const MESSAGE_1: [u8; N0_INS as usize] = [0xA, 0xB, 0xC, 0xD, 0xE, 0xF, 9, 8];

        let mut pubkey = Vec::new();
        for i in 0..N_INS {
            pubkey.push(winter.public_key(i as u32));
        }

        let script = script! {
            {  winter.checksig_verify(winter.pub_key.as_slice()) }// using secret key to generate pubkey

            0xBA OP_EQUALVERIFY
            0xDC OP_EQUALVERIFY
            0xFE OP_EQUALVERIFY
            0x89 OP_EQUALVERIFY
            OP_1
        };

        println!(
            "Winternitz signature size: {:?} bytes per 80 bits",
            script.as_bytes().len()
        );

        let mut sig1 = winter.sign(&MESSAGE_1);
        for i in 0..sig1.len() {
            if sig1[i].len() == 1 && sig1[i][0] == 0 {
                sig1[i] = vec![]
            }
        }
        let exec_result = execute_script_with_inputs(script, sig1);
        assert!(exec_result.success);

        // ============ Test 0 CASE ==============
        const MESSAGE_2: [u8; N0_INS as usize] = [0xA, 0xB, 0x0, 0x0, 0x0, 0xF, 7, 8];

        let mut pubkey = Vec::new();
        for i in 0..N_INS {
            pubkey.push(winter.public_key(i as u32));
        }

        let script = script! {
            {  winter.checksig_verify(winter.pub_key.as_slice()) }// using secret key to generate pubkey

            0xBA OP_EQUALVERIFY
            0x00 OP_EQUALVERIFY
            0xF0 OP_EQUALVERIFY
            0x87 OP_EQUALVERIFY
            OP_1
        };

        println!(
            "Winternitz signature size: {:?} bytes per 80 bits",
            script.as_bytes().len()
        );

        let mut sig = winter.sign(&MESSAGE_2);
        for i in 0..sig.len() {
            if sig[i].len() == 1 && sig[i][0] == 0 {
                sig[i] = vec![]
            }
        }
        let exec_result = execute_script_with_inputs(script, sig);
        assert!(exec_result.success);
    }

    #[test]
    fn test_zero_input() {
        let script = script! {

            0xA OP_EQUALVERIFY
            OP_1
        };

        let input = vec![vec![0xA]];
        let exec_result = execute_script_with_inputs(script, input);
        assert!(exec_result.success);

        let script = script! {

            0x0 OP_EQUALVERIFY
            OP_1
        };

        let input = vec![vec![]];
        let exec_result = execute_script_with_inputs(script, input);
        assert!(exec_result.success);
    }
}
