# Order-64 `[10,6]` certificate bank

The parity-strengthened H16 ledger has exactly six labeled exterior-pair
graphs `R`.  For each one, the outside-block CNF asserts `HB + BC = J` and
that the outside graph `C` has at most one common neighbor per vertex pair.
The completeness CNF asserts the full Boolean `R` ledger and excludes those
six models.

Artifacts live under
`/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-ten-six/`.
Every DRAT was accepted by `drat-trim`; every emitted LRAT was accepted by
`lrat-check`.  The combined CNF and LRAT size is 52,108,455 bytes.

| instance | CNF SHA-256 | LRAT SHA-256 |
|---|---|---|
| r001 | `60a9db3a0e24685ce6ff9abc0f48d5f31ca03f02473fe518ae3b3e29b7395416` | `03a66d915169904a7e2ec81e282b9afa2050bc1f24d17ce933a83db18720025b` |
| r002 | `fa14de698f8e5cf74c0a7804cebd6ca991f18b9a9296411d8fdfae260c6e2c4c` | `611b290f887d14042681904a55464b6503f8acddcc485119d2d08aa8d9ec98e1` |
| r003 | `a50da2b6190b587555705c0642ebfcc467eb182ea5b120f6921aa13aa46bb822` | `89faf2155d25eaf7b7ec2e13e78dc9c974e63a48785100abe9e2db42c450c08e` |
| r004 | `e46a30595388acd7ef9787ec1c7d4ee6b615174f0e7ce2dfa9193bb1286bd496` | `43a511f21085ed486f4eef5ea4027762a3eeacbdc872fc2257f59d352f87dc5c` |
| r005 | `7f07252e8d43560e5c6dff042a997c17c5351481da5334ca618fc03ced5248ca` | `2823ad643d0dabfaca425d6e211507f867a1cc0bc9134c0b8920d06b765708c6` |
| r006 | `ed9ebfe5e4c2655778bd379ae5c7bba72c8b965350ac19d2f81ed82bfc9f249c` | `1a119612b101ddc2b1859dda5d0bf249149f519bf7f94d9451a3e0611543517c` |
| R completeness | `1340370c517be6fd4f8083f1446bead59441f354a2dec60fa9271af0c22a11fd` | `1ec148fe03ef8b79b59d698780cf7f3320b8f34103450695f258bbf765f5e466` |

Regenerate the CNFs with:

```sh
python3 research/problems/erdos-85-wip-01/order64_outside_classifier.py \
  '10,6' --limit 20 --emit-cnf-dir OUT/cnf \
  --emit-r-completeness-cnf OUT/cnf/r_complete.cnf
```

The remaining trusted-proof work is to reproduce these clause generators in
Lean, replay the seven LRATs, and connect the checked unsatisfiability to the
graph-facing `[10,6]` branch of `Erdos85OrderSixtyFourFourSurvivorCensus`.
