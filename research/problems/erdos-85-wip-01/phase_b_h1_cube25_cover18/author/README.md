# Exact CNF cover transfer for 18 archived H1 candidates

## Result and scope

The read-only check found the same 660 clauses used by accepted review 2723 in each of 18 distinct archived candidate bases from the review-2019 binding list. The 11,880 clause occurrences were checked in 0.941 seconds, within the declared 60-second limit. This extends the reviewed propositional coverage argument to 17 additional bases.

Each base therefore implies that some literal in 301–305 and some literal in 456–460 are true. The 25 pairs of unit assumptions cover every satisfying assignment of that base. This follows from the previously reviewed two sequential counters and six-block at-most-one clauses; all relevant signed literals and clause positions are identical.

## Evidence chain

`launch.json` pins the driver, accepted clause certificate, and input-binding list. `check.py` verifies each archived c0 input hash, removes exactly the trailing units 301 and 456, reconstructs the frozen base hash, and checks all 660 required clauses within its declared variable and clause bounds. `results.json` records each tag, input location, hashes and counts.

This application checks c0 and its reconstructed base. The joins for the other 24 cube inputs in each family are inherited from review 2019, not rechecked here. The propositional argument is inherited from accepted review 2723; this packet checks its exact clause containment in each additional base.

## Remaining obligations

Coverage does not establish that any cube is unsatisfiable. This packet supplies no proof verification, fresh canonical regeneration for the additional candidates, new evidence-category admission, H1 exclusion, or Lean theorem. The residual candidate count remains unchanged. No solver or proof replay was launched.

## Per-candidate results

| Tag | Variables | Base clauses | Required clauses |
| --- | ---: | ---: | ---: |
| 033c1d3e7c348135 | 42168 | 613236 | 660 |
| 0bbee37fe45d9447 | 42188 | 613280 | 660 |
| 0db404c43c88e287 | 42184 | 613260 | 660 |
| 0f60c53e650be341 | 42180 | 613256 | 660 |
| 136e336a56215c40 | 42188 | 613272 | 660 |
| 1cd7ab6378689d2f | 42172 | 613248 | 660 |
| 1d0a43cbfa4cb41b | 42084 | 613112 | 660 |
| 1f1eba7d727cf68f | 42192 | 613284 | 660 |
| 38948a3d665b5896 | 42172 | 613240 | 660 |
| 5e5c8470a8b5debc | 42184 | 613268 | 660 |
| 64033f150f4a3d2a | 42176 | 613252 | 660 |
| 6c5673025eb5a43d | 42172 | 613240 | 660 |
| 8c8b1363b570b742 | 42200 | 613300 | 660 |
| 920adad748f4b8dd | 42188 | 613272 | 660 |
| 9eee93ae944b8260 | 42192 | 613284 | 660 |
| b62953fe194fcbd3 | 42172 | 613248 | 660 |
| ca0d0d3a2d00527b | 42172 | 613240 | 660 |
| e6f717d2e69cc8e0 | 42184 | 613268 | 660 |
