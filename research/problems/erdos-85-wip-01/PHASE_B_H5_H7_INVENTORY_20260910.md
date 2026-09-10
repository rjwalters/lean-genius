# Phase B H5/H7 exact inventory — 2026-09-10

This is input and coverage metadata, not a solver result. No solver was launched. The conservative inventory contains **129 H5 root cubes and 28 H7 empty-support class roots**. The full Erdős 85 goal remains open.

## H5

`phase_b_h5_h7/h5-inventory.json` retains every exact ID, signed DIMACS unit list, prospective CNF SHA256 and byte count, base path/hash, emitter source hash and last-change commit. The approved manifest is pinned to `05381a1cf5e80eb480b6e78c4a8dada2573c1cf2f0c55d9ac0bcc4367e3bca76`. All three base files were freshly hash-verified. These use the corrected **29632** variable header; the old 29500-variable H5 encoding is not used.

The 174 roots comprise 58 per cell (`h5_t0`, `h5_t1`, `h5_t2`). The retained historical metadata records 15 direct certificate objects per cell, leaving 43 conservative candidates per cell. This is a conservative historical remainder: later solver results were not freshly censused. Certificate presence alone is not a new proof-validation claim.

Each root hash was freshly calculated using exactly the emitter byte transformation: replace the base header with the same variable count and base clause count plus the number of unit clauses, preserve all other base bytes, then append the units in manifest order. Root files were not materialized or copied. The retained `generate_small_high_cube_jobs.py materialize --manifest MANIFEST --job ID --output OUTPUT` command provides the existing materializer. A host adapter must verify its output against the recorded hash before dispatch.

## H7

`phase_b_h5_h7/h7-inventory.json` retains the complete 43-row mapping as well as the 28 selected rows. For each parent mask the audit found an explicit permutation from parent vertices to classification vertices and checked equality of every edge. The map is bijective on all 43 classes. This avoids incorrectly equating two distinct representative-numbering conventions.

The singleton-capacity certificate excludes 15 classes. Its graph-theoretic justification and finite-certificate review remain in `Q7_H7_UNIVERSAL_SINGLETON_CAPACITY_20260910.md`; this inventory does not replace that argument. The surviving class counts are 7,12,7,2 at edge counts 6,7,8,9. None of the 28 survivors has a direct certificate in the historical parent manifest. All 14 historical direct certificates map into the 15 capacity exclusions; the additional newly removed historical missing root is `cube_F6_t2`.

| Empty edges | Surviving parent type indices |
| --- | --- |
| 6 | 5, 8, 14, 15, 16, 17, 18 |
| 7 | 0, 2, 3, 4, 5, 6, 8, 9, 10, 11, 13, 14 |
| 8 | 0, 1, 2, 3, 4, 5, 6 |
| 9 | 0, 1 |

Every H7 row retains its original parent ID, mask, 21 signed unit clauses, CNF hash and byte count. The compact base was freshly verified against `8bc9b8f15b7f03194f39d208b2c0015e6039e0aac759ccfce0b6415724130eb0`. Replacing its header with `p cnf 17633 720825` and appending each row’s units reproduced all 43 recorded CNF hashes and byte counts. No graph-orbit enumeration or SAT solver was rerun.

The historical 232 adaptive leaves cover 29 formerly missing parents. They are an alternative subdivision, not additional cases to add to these 28 class roots. Phase B should choose this tighter class cover explicitly; timeouts remain UNKNOWN and do not eliminate classes.

## Provenance and host handoff

The JSON files pin the source manifests, mathematical classification certificate, base files and current materializer source. `last_change_commit` means the current source file’s most recent change, not a claim that the historical base was generated at that revision. H5 separately records the historical freight Lean commit and manifest emitter hash. H7 preserves its reviewed parent identity. Fresh regeneration from the complete historical environment was not performed.

Both inventories mark root `cnf_path` as null and `requires_materialization` as true. They are sector evidence, not directly executable `erdos85-verdict-v1` manifests. The host adapter must provide bounded materialization, exact final hashes, generator provenance, caps, cross-check flags and the banked start timestamp. No solver launch is implied by these files.

`build_inventory.py` reproduces the two JSON inventories using the retained local paths. It reads roughly 103 MB of existing base input without copying it and writes less than 200 KB of metadata. `RECEIPT.json` pins this package. Independent review is requested before banking/dispatch.
