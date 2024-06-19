# Bitcommitment Manager

Bitcommitment is a great tool to connect state between different bitcoin script, but costs huge script size and stack limit. This crate implements a manager for bitcommitment, making it more compacted and more convenient.

## How to use it?

A multi-layer loop may produce too much scripts. E.g., this example below: `single script_size = 2501, script_info_cnt = 100, total = 250100`

```rust
let mut scripts = vec![];
let mut sum: u32 = 0;
for i in 0..10 {
    // more loop will lead to be over the stack limit
    let added: u32 = i;
    for j in 0..10 {
        // record prestate
        let pre_sum = sum;
        sum += added;
        // record state
        scripts.push(script_info!(
            &format!("add_{}_{}", i, j),
            script! {
                OP_ADD
            },
            [added, pre_sum],
            [sum]
        ));
    }
}
```

After using the compiler `SimplePlanner`, make it: `single combined script_size = 2974, combined_script_cnt = 17, total = 50558`

```rust
let (leafs, _) = SimplePlanner::compile_to_eq(scripts);
```

## Futures

- [x] Basic Script Info
- [x] Combine small scripts (Simple Planner)
- [ ] Split large scripts
- [ ] Integrity verification
- [ ] More optimized Planners
    - [ ] When build connection with different input and outputs, not just `OP_DUP`, others op_code can be used (`OP_ADD1`, `OP_SUB1`, ...)
    - [ ] Reduce more intermidiate state by marking it private