# Full representative reduction after the first terminal certificate

The remaining full representative-pair list has **275 entries**. This removes
pair `(1,14)` from the previously checked 276-entry list. Full representative 1
is definitionally the compact U code `(6,6,15)`; the complete fixed-pair coverage
and rejection certificate excludes every admissible, externally capped cross
at R representative 14.

`TerminalReduction.lean` imports that concrete exclusion theorem. It has no
unproved first-pair rejection premise. The original graph hypotheses and the
same cross, domain, external-cap, and joint-witness facts are preserved by the
remaining-pair membership and actual-graph witness theorems. The final exclusion
theorem still explicitly requires false-search results for all **275 remaining
pairs**. Those results are not supplied here, and Erdős 85 remains open.

The six exported theorems passed ordinary Lean checking, with only `propext`,
`Classical.choice`, and `Quot.sound`. The retained `compile.log` records that
source check. `run.json` records the successful portable runner check of the
five-export prior reduction and this six-export reduction. `RECEIPT.json` pins
the files and the prior reduction source.

## Reproduction

Run under `lake env` from the repository `proofs` directory. First obtain
verified retained build directories using the documented checkers in:

- [Full U coverage](../compact_u_orbits/full_coverage/README.md).
- [Full block pruning](../full_block_pruning/README.md), retaining its dependency
  outputs with `--build-dir`.
- [Fixed-pair rejections](../fixed_pair_rejections/README.md).
- [Fixed-pair coverage and final exclusion](../fixed_pair_coverage/README.md).

Then run:

```sh
lake env python3 ../research/problems/erdos-85-wip-01/full_terminal_pruning/check.py \
  --full-u-build /verified/full-u-build \
  --pruning-build /verified/full-block-pruning-build \
  --pair-coverage-build /verified/pair-coverage-build \
  --pair-rejections-build /verified/pair-rejections-build \
  --pair-exclusion-build /verified/pair-exclusion-build \
  --build-dir /new/empty/terminal-pruning-build
```

The runner puts its fresh output directory first on `LEAN_PATH`, verifies the
two source hashes, and recompiles the prior reduction as `FullBlockReduction`
to avoid module-name collisions. It then compiles `TerminalReduction` and checks
all 11 printed exports. Logs, objects, and `RESULT.json` remain in the output
directory. If `--build-dir` is omitted, a new temporary directory is retained.
The optional `--representatives-build` supports older staged rejection builds
whose representative objects are in a separate directory; the portable
rejection package's combined build does not need it.
