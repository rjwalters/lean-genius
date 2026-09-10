# Full-case reduction from 275 to 261 pairs

CapacityReduction removes the 13 certified subset-capacity pairs and U32/R14 from the prior 275-pair list. Lean checks the resulting cardinality of 261. The representative equalities connect the numerical exclusions to the actual full-case witness; the same cross and its hypotheses are retained.

The source passed ordinary Lean checking with seven printed exports using only standard axioms or subsets. A fresh run of the portable checker also passed in 40.35 seconds. Independent review 1987 is pending. The final `actual_full_excluded_pruned` theorem still requires rejection of the remaining 261 pairs; it does not prove the full case or Erdős 85. The deficient-case list remains at 1554.

Prerequisites are verified builds of [the prior reduction](../full_terminal_pruning/README.md), [the thirteen counting certificates](../full_subset_capacity/README.md), and [U32 coverage](../zero32_coverage/README.md), together with their transitive prerequisite build directories.

From the repository proofs directory, pass every prerequisite build directory in dependency search order:

```sh
lake env python3 /path/to/full_capacity_pruning/check.py \
  --dependency-build /verified/subset-build \
  --dependency-build /verified/zero32-build \
  --dependency-build /verified/terminal-build \
  --dependency-build /verified/other-transitive-build \
  --build-dir /new/empty/build-directory
```

Repeat `--dependency-build` for each transitive build. The retained run receipt records the complete directories used in this session. The checker verifies the source hash, rejects nonempty output directories, puts fresh output first in LEAN_PATH, and checks seven standard-axiom exports with a 180-second process bound. It retains the log and terminal receipt. Prerequisite builds must already have passed their own checks.
