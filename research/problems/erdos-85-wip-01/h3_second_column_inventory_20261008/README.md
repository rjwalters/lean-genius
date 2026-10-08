# Second-column diagnostic for forced-first-column H3 pairs

Status: **cloud PASS; independently audited candidate inventory**.

| Case | Static pairs | Both prefix gates pass |
| --- | ---: | ---: |
| Full U3/R3 | 36 | 36 |
| Deficient U26/R2 | 40 | 40 |

Both have the unique empty first column. This gives a 36-way and a 40-way
split for separate branch checks. No branch rejection or speedup follows.
Job `20261008T042508-erdos85__h3-first-column-20261008-178693` passed at
`cfae166b13c`, with 16 GiB, one compiler thread, and a 15-minute cap.
The diagnostic took 5.01 seconds after a 6.20-second dependency check.
`evidence/` retains copied source, complete logs, run receipt, and independent
audit. The cloud object hash and source/log hashes match the receipt; the
first-column masks/gates agree with the earlier audited inventory.

This diagnostic enumerates the exact static first/second-column Cartesian
product for Full U3/R3 and Deficient U26/R2, then evaluates both prefix gates.
The first-column inventory already found one empty candidate in each case.
Fixed U/R matrices are cached before evaluation. No remaining DFS branch,
concrete rejection theorem, or runtime speedup is evaluated.

`Inventory.lean` uses the same U/R definitions and representatives as the
verified first-column diagnostic. `check_inventory.py` builds dependencies,
compiles a copied source in a fresh output directory, validates the Cartesian
product and gate types, and records source/object/log hashes and timings.
The second-column decomposition itself was separately verified with only
standard axioms; see `../h3_second_column_20261008/`.

Run on the existing cloud first-column worktree, from `proofs`, with 16 GiB,
one compiler thread, and a 15-minute timeout:

```sh
lake env python3 ../research/problems/erdos-85-wip-01/h3_second_column_inventory_20261008/check_inventory.py --output ../research/problems/erdos-85-wip-01/h3_second_column_inventory_20261008/_build/cloud-first
```
