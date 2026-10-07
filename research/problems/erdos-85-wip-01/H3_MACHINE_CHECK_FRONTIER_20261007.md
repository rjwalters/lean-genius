# H3 machine-check frontier, 7 October 2026

This source audit corrects the H3 triple estimates in
`UNAMBIGUOUS_UPPER_BOUND_PLAN_20261007.md`. It does not close either H3 cell.
Historical build statements below come from the retained source packages and
their receipts; they are not claims of a fresh rebuild today.

## Soundness already proved

The `hsound : ThreeHighTerminalSound accept` premise is already discharged for
several executable choices in `proofs/Proofs/`:

- `Erdos85ThreeHighClosedJointSearch.lean`:
  `threeHighClosedJointSearch_sound`.
- `Erdos85ThreeHighSeparatedJointSearch.lean`:
  `threeHighSeparatedJointSearch_sound`.
- `Erdos85ThreeHighCachedSupportClosure.lean`:
  `threeHighCachedSeparatedJointSearch_sound` (caches adjacency and triple lists).

The external search also has a proved implementation:
`threeHighStaticCapacityColumnDFS_sound` in
`Erdos85ThreeHighStaticCapacityColumnDFS.lean`. It preserves both cross-domain
membership and the external block cap. Combining this with the cached terminal
requires only a small implication lemma, not a new graph-to-core proof.

## Symmetry coverage already proved

The top-level `compact_u_orbits/README.md` describes an early Python experiment.
Its later child packages contain Lean coverage and must be consulted as well:

| Package | Proved interface / scope |
| --- | --- |
| `compact_u_orbits/full_coverage/` | `FullURestrictedAssembly.covered`, 55 full-U representatives; 100 retained coverage shards |
| `compact_u_orbits/deficient_coverage/` | `DeficientUNormalizedAssembly.covered`, 370 deficient-U representatives; 200 retained coverage shards |
| `full_orbit_transport/` | `actual_full_witness`, actual graph to 55 × 13 U/R pairs with the same joint witness |
| `deficient_orbit_transport/` | `actual_deficient_witness`, actual graph to 1,554 structurally pruned U/R pairs with the same joint witness |

The complete deficient coverage is connected by the later transport package;
the older pruning README's statement that coverage is separate is not the final
status of that chain.

## Remaining finite checks

The full branch has the following retained reductions:

1. `full_orbit_transport/`: 715 pairs.
2. `full_orbit_pruning/`: 565 pairs.
3. `full_block_pruning/`: 276 pairs.
4. `full_terminal_pruning/`: 275 pairs, after the complete fixed-pair exclusion
   at U index 1 / R index 14.
5. `full_capacity_pruning/`: 261 pairs, after 13 subset-capacity exclusions and
   U index 32 / R index 14.

The deficient branch retains 1,554 pairs. The final exclusion theorems still
take false-search premises for these pairs. The Python paper census's 3,337
U/R cases uses different normalization, so it is not the number of residual
Lean obligations. No conversion of Python output into Lean truth is justified
merely by comparing totals.

The retained coverage packages use ordinary `decide` and report only the three
standard axioms. Compiled `native_decide` can be a faster route for new finite
checks, but adds its native-computation axiom and must be reported separately.
An unchecked `#eval` result would be diagnostic only.

## Terminal-condition mismatch

The Python verifier `verify_q7_h3_triple_m2_singleton_exclusion.py` checks
`y != x` when requiring a compatible neighbor in each of the three colors.
The same-color case is therefore a real condition.

`threeHighListedJointSearch` checks family compatibility only between different
colors. `encodedFamilyCompatibility` also permits the selected triple `T` to
equal `S`. `threeHighTripleSupportPass` explicitly skips the same-color case.
Thus the existing terminal soundness theorems are valid, but the Python
exhaustions do not by themselves imply these weaker Lean searches return false.
Some pairs may still be rejected by the weaker tests; universal rejection must
be checked rather than assumed.

`Erdos85OrderFortyNineThreeHighTripleDistinctColorNeighbor.lean` proposes the
stronger graph-side fact. The existing ordinary-neighbor theorem supplies a
vertex `y ≠ x` with both coordinate sets of cardinality three. The existing
C4-free intersection bound limits their intersection to one, so the coordinate
sets cannot be equal. This yields `encodedDistinctFamilyCompatibility` for all
color pairs, including equal colors. Compilation is pending. Connecting that
stronger condition through the compact joint-witness and orbit-transport
interfaces remains separate work.

## Current pilot

`Erdos85ThreeHighNativePairSearch.lean` combines the existing sound static
column search and cached family search, with fixed U/R adjacency and the fixed
U block-cap check cached outside the prefix traversal. Its equality and
soundness lemmas are separate from the finite check in
`Erdos85ThreeHighNativeTerminalPilot.lean`. Its proposed new pair uses full compact
U code `(6,6,15)` (full representative 1) and secondary representative 15.
This differs from the already certified pair `(1,14)`. Independent Python
set arithmetic on the retained Lean tables reproduced the full counts above,
confirmed all 13 subset-capacity removals, and confirmed `(1,15)` remains in the
261-pair set. The deficient tables independently give 142 unconditional U
exclusions and 90 further conditional exclusions, reproducing 1,554 pairs.
These source-table checks are not new Lean coverage proofs.

The first two bounded builds did not reach the proposed new rejection theorem.
No new pair exclusion is claimed from those attempts.

The first dependency build used `LEAN_MEMORY_LIMIT=8192` and exhausted that
limit at approximately 390 seconds before reaching the pilot. Many simultaneous
compiler processes stalled while the cgroup recorded over one million memory
limit events. Commit `34caae65a09` adds an optional `LEAN_NUM_THREADS` environment
passthrough to `proofs/scripts/docker-build.sh`. Retrying with
`LEAN_NUM_THREADS=2` retained the 8 GiB cap, ran two compiler processes, and
completed the previously stalled modules. Shell syntax, invalid-value rejection,
and the in-container environment were checked. This is a build-resource fix,
not additional mathematical evidence.

The two-thread retry reached the ten-minute cap (exit 124) after completing
`Erdos85OrderFortyNineThreeHighTripleSecondaryAdmissibility`, at 8,947/8,973
reported build jobs. It did not reach the pilot module. The container was removed
and the single build slot handed to the H7 owner. These timings include dependency
compilation and are not timings for the finite search.

## Remaining H3 scope

Even completing this triple branch would leave the pair-profile exclusion and
the final stratum assembly. The paper should retain its current disclosure that
H3's overall exclusion is based on reviewed reductions and Python computations.
