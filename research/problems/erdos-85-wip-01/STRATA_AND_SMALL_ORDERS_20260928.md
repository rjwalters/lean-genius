# The order-49 strata and the small-order exact values, from the Lean source (2026-09-28)

All names are declarations in `proofs/Proofs/` on `erdos85/integration` (verified 2026-09-28 by grep; the census-facing ones are in the cold-build cone of `AXIOM_AUDIT_COLD_20260927`).

## What a "high" vertex is and why the strata are h ∈ {1, 3, 5, 7}

- `orderFortyNineHighVertices G` (`Erdos85OrderFortyNineIncidence.lean`) is the finset of vertices of **degree exactly 8**. In a hypothetical C4-free graph on 49 vertices with minimum degree 7, every degree is 7 or 8 (the Lean development derives this from the C4-free codegree bound), so the "high count" h is the number of degree-8 vertices; the remaining 49 − h vertices have degree 7.
- `OrderFortyNineStratumExcluded h` (`Erdos85OrderFortyNineStrataCapstone.lean`) states: for every `G : SimpleGraph (Fin 49)` that is C4-free with all degrees ≥ 7 and exactly h high vertices, `False`.
- `orderFortyNine_card_high_eq_one_or_three_or_five_or_seven_or_nine` proves that such a graph has h ∈ {1, 3, 5, 7, 9} (parity: 49 vertices with degrees in {7, 8} force an odd number of degree-8 vertices; an upper bound from the C4-free edge count keeps h ≤ 9).
- `orderFortyNineStratumExcluded_nine` proves the h = 9 stratum impossible uniformly in Lean (`false_of_orderFortyNine_nine_high`), with no external input.
- `not_c4FreeMinDegreeWitness_fortyNine_seven_of_strata (h1) (h3) (h5) (h7) : ¬ C4FreeMinDegreeWitness 49 7` composes the four remaining strata. This is the exhaustiveness statement the paper cites: the case split is the theorem's own interface, and only the four stratum exclusions are inputs.

## How each stratum is closed (interface level)

| h | Lean cell structure | Evidence for the inputs |
|---|---|---|
| 1 | `orderFortyNineStratumExcluded_one_of_pureFamilies`: five ordered one-high family profiles; the H1 capacity rows (13,351 slots) refine them | the census (`CENSUS.md`): 1,257 rows = 96 certificate-verified + 1,161 two-solver UNSAT; the row-to-stratum assembly is an open formal obligation |
| 3 | `orderFortyNineStratumExcluded_three_of_tripleCells`: triple-system cells t = 0, 1 | `orderFortyNineGeneratedCanonicalSatCnf` applied to `threeHighRepresentativeMasks`; checked LRAT proofs for both cells (`PHASE_B_H1_H3_INVENTORY_20260910.md`, `Q7_H1_H3_SQUEEZE_20260910.md`) |
| 5 | `orderFortyNineStratumExcluded_five_of_tripleCells`: cells t = 0, 1, 2 | `fiveHighRepresentativeMasks`; reviewed paper/computation cover (`PHASE_B_H5_H7_INVENTORY_20260910.md`, `Q7_H5_H7_SQUEEZE_20260910.md`) |
| 7 | `orderFortyNineStratumExcluded_seven_of_tripleCells`: cells t = 0 … 7 from `orderFortyNine_highIncidence_profile_of_seven_high` (the seven-high incidence profile bounds the triple count by 7) | `H7_CLOSURE_20260915.md`: 28 surviving structural roots after 15 singleton-capacity exclusions, all excluded at the paper/computation level; the Lean capstone `orderFortyNineStratumExcluded_seven_of_emptyCubeEvidenceVectors` (four evidence vectors of lengths 19/15/7/2) is not instantiated |
| 9 | `orderFortyNineStratumExcluded_nine` | proved in Lean, no input |

The H3/H5 consumer route is `not_c4FreeMinDegreeWitness_fortyNine_seven_of_smallHighLratChecks` (`Erdos85OrderFortyNineSmallHighVerifiedFrontier.lean`), whose docstring records that "the h=3 and h=5 graph-normalization obligations have been discharged" and exposes five concrete LRAT checks plus the independent h = 1 and h = 7 inputs; the cube route `not_c4FreeMinDegreeWitness_fortyNine_seven_of_smallHighCubeBaseUnsat` reaches the same conclusion from seven base-CNF `Unsat` proofs.

## Small orders, Lean-checked exact values (`Erdos85Problem.lean`)

- `minDegreeForC4_fifteen : minDegreeForC4 15 = 5` (lower side `five_le_minDegreeForC4_fifteen` via the explicit 4-regular C4-free graph `fifteenRegular`; upper side by the C4-free counting bound).
- `minDegreeForC4_sixteen : minDegreeForC4 16 = 5` (lower side via `sixteenRegular`, 4-regular C4-free).
- So f(15) = f(16) = 5: no drop at 15→16, and the q = 4 analogue of A-REG (no C4-free 4-regular graph on 16 vertices) is false because `sixteenRegular` is one.
- Also in the tree: `minDegreeForC4_thirtytwo_eq_six : minDegreeForC4 32 = 6` (`Erdos85FiniteSigningClosure.lean`).

## Order-48 non-isomorphism receipt

`sat49/verify_boza48_nonisomorphism.py` rerun 2026-09-28 (`BOZA48_NONISOMORPHISM_RECEIPT_20260928.txt`): PASS, the checked witness is non-isomorphic to all 10 graphs of the Afzaly–McKay archive `c4_n48e168.maybe.s6` (sha256 `7bc1de35…`), the unique 7-regular archive graph being index 9. NetworkX 3.6.1.
