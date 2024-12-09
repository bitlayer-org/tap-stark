# TapStark

TapStark is a Bitcoin-friendly proof system enabling on-chain verification through BitVM2 paradigm and Taptree commitment scheme. Built upon Plonky3, it operates independently of OP_CAT.

## Core Components

- **Polynomial Commitment**: Combines Taptree commitment with bit commitment
- **Cryptographic Hash**: Uses Blake3 for permutation hashing
- **Low Degree Testing**: Implements FRI protocol
- **STARK Protocol**: Follows [Plonky3's uni-stark](https://github.com/Plonky3/Plonky3/tree/main/uni-stark) approach
- **Verification DSL**: Custom domain-specific language for Bitcoin script generation

## Documentation

- For a conceptual overview, read our [introductory article](https://blog.bitlayer.org/introduce-bf-stark/)
- For technical details, see our [comprehensive paper](./doc/TapSTARK.pdf)

## Domain Specific Language (DSL)

Our DSL facilitates rapid development of Bitcoin verifiers for TapStark. It serves two key purposes:

1. Streamlines verifier script development
2. Automates constraint script generation via [ScriptAirBuilder](./script_expr/src/script_builder.rs)

### Supported Operations

The DSL supports the following operations over babybear field and its extension:

```rust
pub(crate) enum StandardOpcodeId {
    Add,
    Mul,
    Sub,
    Neg,
    Equal,
    EqualVerify,
    NumToField,
    Constant,
    ExpConst,
    IndexToRou,
    Lookup,
    InputVarMove,
    InputVarCopy,
    Table,
    Square,
    Double,
    Blake3Perm,
    ToSample,
    SampleBase,
    SampleExt,
    ReverseBitslen,
}
```

### Usage Example

```rust
// Initialize field elements
let vec = vec![
    BabyBear::from_canonical_u32(1),
    BabyBear::from_canonical_u32(2),
    BabyBear::from_canonical_u32(3),
    BabyBear::from_canonical_u32(4),
    BabyBear::from_canonical_u32(5),
];

// Setup environment
let mut stack = StackTracker::new();
let bmap = BTreeMap::new();

// Demonstrate table lookup and arithmetic
let table = Dsl::from_table(&vec);
let index = 4;
let m = table.lookup(index, vec.len());

let a = Dsl::constant_f(BabyBear::one());
let b = Dsl::constant_f(BabyBear::two());
let c = a + b + m;

// Verify computation
let equal = h.equal_for_f(Babybear::from_canonical_u32(7));
let res = equal.express_with_optimize();
println!("Optimized script length: {:?}", res.0.get_script().len());
let res = res.0.run();
assert!(res.success);
```

### Data

| bit security(conjectured soundness with 36 pow bits) | log blowup factor | query_num | trace        | table height(degree) | table width | public inputs | total u32 num(intermediate states) | fri u32 num(intermediate states) | total script len | script len for fri query | verify trace constraint script len | compute quotient poly | challenge script size |
| ---------------------------------------------------: | ----------------: | --------: | :----------- | :------------------- | ----------: | ------------: | ---------------------------------: | -------------------------------: | :--------------- | :----------------------- | :--------------------------------- | :-------------------- | :-------------------- |
|                                                   91 |                 2 |        28 | Fibonacci    | 1 << 3               |           2 |             3 |                                360 |                              341 | 12177kb          | 28 x 428 = 11984 kb      | 120kb                              | 73kb                  | nan                   |
|                                                   67 |                 2 |        16 | Fibonacci    | 1 << 3               |           2 |             3 |                                300 |                              284 | 7041kb           | 16 x 428 = 6848 kb       | 120kb                              | 73 kb                 | nan                   |
|                                                   99 |                 4 |        16 | Fibonacci    | 1 << 3               |           2 |             3 |                                300 |                              284 | 7041 kb          | 16 x 428 = 6848 kb       | 120kb                              | 73kb                  | nan                   |
|                                                   67 |                 2 |        16 | Fibonacci    | 1 << 4               |           2 |             3 |                                424 |                              408 | 8113 kb          | 16 x 495 = 7920 kb       | 120kb                              | 73kb                  | nan                   |
|                                                   67 |                 2 |        16 | Fibonacci    | 1 << 5               |           2 |             3 |                                490 |                              471 | 9185 kb          | 16 x 562 = 8992 kb       | 120kb                              | 73kb                  | nan                   |
|                                                   67 |                 2 |        16 | Fibonacci    | 1 << 10              |           2 |             3 |                                829 |                              810 | 14593kb          | 16 x 900 = 14400 kb      | 120kb                              | 73kb                  | nan                   |
|                                                   67 |                 2 |        16 | Fibonacci    | 1 << 11              |           2 |             3 |                                956 |                              937 | 15681 kb         | 16 x 968 = 15488 kb      | 120kb                              | 73kb                  | nan                   |
|                                                   99 |                 4 |        16 | Recursive R0 | 1 << 18              |         163 |           nan |                               2904 |                             1600 | 129.44 MB        | 16 x 1444 = 23104 kb     | 100.878mb                          | 6mb (s=5)             | 2.2 mb                |

## TODO List

### Taptree Commitmtment

- [x] support taptree commmitment
- [x] intergate into fri
  - [x] genereate new taptree for per-query
- [x] intergate into pcs
- [x] intergate into uni-stark

### ScriptExpr Verifier

- [x] uni-stark script_expr
  - [x] compute selector script_expr
  - [x] compute quotient script_expr
  - [x] compute constraints script_expr
- [x] two-adic-pcs script_expr
- [x] fri script_expr
- [x] challenge script_expr

### ScriptExpr

- [x] support input variable
- [x] automatic management of input variables
  - [x] automatic computation of the number of inputs
- [x] implement copy variable to optimize the compiler
- [ ] Implementing automatic segmentation tool
  - [ ] bitcommitment assign
  - [ ] extract intermidiate value
- [x] add verify hint gadget

# LICENSE

This repository is under the MIT license. See `LICENSE.txt` for more information.
