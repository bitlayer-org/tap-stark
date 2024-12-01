use std::collections::HashMap;

pub struct ValueCounter {
    value_num: u32,
    value_register: HashMap<u32, bool>,
}

impl ValueCounter {
    pub fn new() -> Self {
        ValueCounter {
            value_num: 0,
            value_register: HashMap::new(),
        }
    }

    fn set_value_bitcomm(&mut self, value: u32) {
        self.value_num += 1;
        let res = self.value_register.insert(value, true);
        assert!(res.is_none());
    }

    fn get_value_bitcomm(&self, value: u32) -> Option<&bool> {
        self.value_register.get(&value)
    }

    pub(crate) fn get_or_set(&mut self, value: u32) -> bool {
        let exist = self.get_value_bitcomm(value);
        if exist.is_some() {
            *exist.unwrap()
        } else {
            self.set_value_bitcomm(value);
            true
        }
    }

    pub fn get_value_num(&self) -> u32 {
        self.value_num
    }
}
