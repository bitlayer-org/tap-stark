use std::fmt::Debug;

use bitcoin::hex::DisplayHex;
use rand::{thread_rng, Rng};

pub trait SecretGen: Debug + Clone + Default + PartialEq + Eq {
    fn gen() -> String;
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ConstantSecretGen;

impl SecretGen for ConstantSecretGen {
    fn gen() -> String {
        // temporary secret
        "0000".to_owned()
    }
}

// not security enough
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ThreadSecretGen;

impl SecretGen for ThreadSecretGen {
    fn gen() -> String {
        let s: String = rand::thread_rng()
            .sample_iter::<char, _>(rand::distributions::Standard)
            .take(20)
            .collect();
        s.as_bytes().to_lower_hex_string()
    }
}

// TODO: find some more security random source
