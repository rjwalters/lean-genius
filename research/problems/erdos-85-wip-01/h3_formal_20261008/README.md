# H3 distinct-witness transport, 8 October 2026 (UTC)

Eight new theorem exports compile with only `propext`, `Classical.choice`, and
`Quot.sound`. Together with the fourteen exports in `../h3_formal_20261007/`,
these retain the Python verifier's distinct-neighbor condition from an actual
graph through compact coordinates and a supplied complete orbit cover.
**No new concrete pair exclusion or H3 stratum exclusion is established.**

## Committed source and checks

| Commit | Module suffix | Exports |
| --- | --- | --- |
| `fad45a74bab` | `DistinctOrbitTransport` | 1 |
| `94ba1ea340c` | `DistinctOrbitCandidates` | 2 |
| `1dc54f05dd0` | `DistinctRepresentativeWitness` | 4 |
| `e39c5dc949e` | `DistinctBlockPermutationTransport` | 1 |

All modules are `proofs/Proofs/Erdos85ThreeHigh<SUFFIX>.lean`.
`receipt.json` records commands, source/toolchain/manifest hashes, and the eight
axiom exports. `axioms.txt` is an excerpt, not a complete build log.

The representative target initially reached its five-minute limit compiling
cold dependencies. Its retry passed. The separate block-permutation target also
passed. Builds used the repository Docker runner, 8 GiB, and one Lean thread;
no host Lean compiler or new finite `native_decide` check was used.

## Concrete census integration still to check

The new representative theorems deliberately take an explicit `covered`
premise. The existing retained assemblies provide the matching interfaces:

- Full: `threeHigh_full_distinct_representative_witness` takes
  `FullURestrictedAssembly.representative` and `FullURestrictedAssembly.covered`.
- Deficient: `threeHigh_deficient_distinct_representative_witness` takes
  `DeficientUNormalizedAssembly.representative` and
  `DeficientUNormalizedAssembly.covered`.

The concrete applications must be compiled with those research packages and
retain the strong witness alongside cross-domain membership and external caps.
They have not been freshly compiled as part of this contribution.

The full branch has another transport step in `full_block_orbits/Certificate.lean`:
`FullUBlockOrbits.joint_transport` changes U representative and cross matrix.
Do not forget the strong witness before that step. A distinct variant can use
`threeHighBlockPermutation_distinct_joint_transport` with the existing
`label`, `blockLabel`, `rows_checked`, and `adjacency_checked` certificates.
Its target is the same `target r`; `target_mem` gives membership in the block
representative set.

After that transport, the existing full terminal/capacity exclusions can use
`hJoint.forget _` while retaining the original strong `hJoint` for the final
search. The deficient pruning theorem `DeficientUOrbitPruning.actual_pair_mem`
requires the degree class, cross-domain membership, and external cap only;
it does not change the witness. This describes the source interfaces; it is
not a substitute for compiling the concrete applications.

The remaining finite sets still have 261 full and 1,554 deficient pairs.
The old U1/R15 pilot remains unverified after its four-minute timeout. The H3
pair-profile branch and final stratum assembly also remain open.

## Squad handoff

The cloud builder's read-only status on 8 October confirmed the H7 counting
job exited zero, while job
`20261007T233905-erdos85__h7t0-formal-20261007-14715` (MixedCapstone) was running.
This is a timestamped observation, not a claim that the job remains live or
that the H7 stratum is closed. Claude requested a LIVE announcement before
launching our H3 pilot; no H3 cloud job was submitted in this round.
