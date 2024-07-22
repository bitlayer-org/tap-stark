# Bf-Stark

Bf-Stark is a bitcoin friendly proof-system which can be verified on chain based Bitvm2 Paradigm and Taptree Commitment.
Bf-Stark is also modified based on Plonky3.
Bf-Stark does not need to depend on the implementation of OP_CAT.
### Taptree Commitmtment 
- [x] support taptree commmitment
- [x] intergate into fri
    - [ ] genereate new taptree for per-query 
- [x] intergate into pcs
- [x] intergate into uni-stark

### ScriptExpr Verifier 
- [x] uni-stark script_expr
    - [x] compute selector script_expr 
    - [x] compute quotient script_expr
    - [x] compute constraints script_expr
- [ ] two-adic-pcs script_expr 
- [ ] fri script_expr 
- [ ] challenge script_expr

### ScriptExpr
- [x] support input variable 
- [ ] automatic management of input variables
- [ ] implement copy variable to optimize the compiler
- [ ] Implementing automatic segmentation tool 
    - [ ] bitcommitment assign
    - [ ] extract intermidiate value 
- [ ] add verify hint gadget


