![BF-STARK (Bitcoin Friendly STARK) powered by Bitlayer]()

BF-STARK  is a Plonky3 based toolkit for verifiying STARK proof on the Bitcoin network. 


## Status
Primitives
- [x] BF-fields
- [x] BF-hash and challenger traits
Scripts
- [x] BitCommitment
- [x] Hashes
  - [x]Blake3
- [x] 
FRI: Taptree based FRI prover and verifier
- [X]Taptree prover
- [x]Taptree verifier
- [x]TreeBuilder
PCS: Taptree based polynomial commitment scheme
- [] WIP
## Benchmark
WIP
## Known issues


## License
WIP




## Guidance for external contributors

WIP
### General guidance for your PR
The PR guidence is very well written by Plonky team so we just borrowed

Obviously PRs will not be considered unless they pass our Github
CI. The Github CI is not executed for PRs from forks, but you can
simulate the Github CI by running the commands in
`.github/workflows/ci.yml`.

Under no circumstances should a single PR mix different purposes: Your
PR is either a bug fix, a new feature, or a performance improvement,
never a combination. Nor should you include, for example, two
unrelated performance improvements in one PR. Please just submit
separate PRs. The goal is to make reviewing your PR as simple as
possible, and you should be thinking about how to compose the PR to
minimise the burden on the reviewer.



#### The PR fixes a bug

In the PR description, please clearly but briefly describe

1. the bug (could be a reference to a GH issue; if it is from a
   discussion (on Discord/email/etc. for example), please copy in the
   relevant parts of the discussion);
2. what turned out to the cause the bug; and
3. how the PR fixes the bug.

Wherever possible, PRs that fix bugs should include additional tests
that (i) trigger the original bug and (ii) pass after applying the PR.


#### The PR implements a new feature

If you plan to contribute an implementation of a new feature, please
double-check with the Polygon Zero team that it is a sufficient
priority for us that it will be reviewed and integrated.

In the PR description, please clearly but briefly describe

1. what the feature does
2. the approach taken to implement it

All PRs for new features must include a suitable test suite.


#### The PR improves performance

Performance improvements are particularly welcome! Please note that it
can be quite difficult to establish true improvements for the
workloads we care about. To help filter out false positives, the PR
description for a performance improvement must clearly identify

1. the target bottleneck (only one per PR to avoid confusing things!)
2. how performance is measured
3. characteristics of the machine used (CPU, OS, #threads if appropriate)
4. performance before and after the PR


### Licensing

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the
#TODO , shall be dual licensed as above, without any
additional terms or conditions.