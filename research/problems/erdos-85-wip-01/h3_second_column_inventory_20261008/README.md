# Second-column diagnostic for forced-first-column H3 pairs

Status: **prepared; cloud result pending**.

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
