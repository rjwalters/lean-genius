# Accepted cached a7 pair-row host API and independent verifier

Producer review **2669 PASS** and verifier review **2670 PASS** accept this
canonical-a7 API for correctness under its stated input and coverage premises.
Pair-row templates are computed in the fixed base graph and filtered as host
choices are added. Future-host masks conservatively cover all remaining options.
Only exhausted empty domains prune; one shared node/deadline budget propagates
exhaustion as UNKNOWN. The API explicitly excludes a6 input layouts.

The independent checker combines the unchanged accepted 2124 structural cover
checker with separately written increasing-vertex singleton/pair row enumeration.
Its tests cover 33 saved records/controls, 2,930 negative endpoints, a positive
fixed leaf, and five corrupted certificates. A fresh cached-producer build
reproduces four fixed-assignment receipts. Verifier review 2670 adds independent
compilation, relabelled controls and explicit UNKNOWN/corruption checks.

At the original 100,000-unit calibration, the baseline had 12 UNKNOWN inputs;
the cached version completed two F5 inputs while two F5 and all eight F0 inputs
remained UNKNOWN. This archive is correctness evidence, not a whole F0 exclusion.
The separate `q7_h7_f0_pairrow_calibration` archive records the declared normalized
budget experiment. No Lean kernel proof or arbitrary-CNF UNSAT result follows.

`producer/` copies exactly 25 pinned producer files plus its original manifest.
`verifier/` copies exactly 12 pinned verifier files plus its manifest. `review/`
contains accepted room records and the independent verifier review artifacts.
All source bytes are preserved, including earlier candidate wording and the
verifier's initial failed harness launch. Absolute paths in original scripts
are provenance; their source hashes determine identity.
