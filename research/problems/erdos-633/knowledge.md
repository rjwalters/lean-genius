# Erdős #633 — Square-Only Triangle Dissections (knowledge)

## State
- OPEN ($25). Gallery file `proofs/Proofs/Erdos633Problem.lean`, badge `wip`, **4 real sorries** (was 5; `similar_dissection_characterization` filled as a vacuous model-fact this session).
- Model: BOTH `CongruentDissection` (congruent) and `CanDissectIntoSimilar` (similar) encode ONLY area-compatibility (`area T = n·area S`) + side-ratio similarity. Neither encodes a real tiling.

## Key structural fact (CRITICAL)
The model **over-counts**: by `Triangle.area_scale`, the scaled copy `T.scale (1/√n)` satisfies both numeric conditions for *every* `n ≥ 1`. Hence `DissectionCounts T = {n | n ≥ 1}` for every triangle, so the square-only direction is **model-false**, not just unproved.

## Session 2026-06-26 (researcher-3)
Turned the informal over-counting note into proved theorems (mirroring the already-verified `universal_square_dissection` / `equilateral_dissects_to_3`):
- `all_counts_achievable (T) (n) (hn : n ≥ 1) : CanDissectInto T n` — witness `T.scale (1/√n)`.
- `dissectionCounts_eq : DissectionCounts T = {n | 1 ≤ n}`.
- `not_isPerfectSquare_two : ¬ IsPerfectSquare 2`.
- `no_square_only_in_model (T) : ¬ HasSquareOnlyProperty T` (2 is achievable & non-square).
Added doc notes to `soifer_square_only` and `erdos_633` flagging they are model-false (refuted by `no_square_only_in_model`).

## Session 2026-06-26 (researcher-1) — CORRECTION + similar-model diagnosis
The prior note (below) called the two `CanDissectIntoSimilar` sorries "the hard
#634 content." **That was a mischaracterization.** `CanDissectIntoSimilar` is
*also area-only*, so it over-counts identically to the congruent model. Proved:
- `canDissectIntoSimilar_of_one_le (T) (n) (hn : n ≥ 1) : CanDissectIntoSimilar T n`
  — witness `T.scale (1/√n)` (the similar analogue of `all_counts_achievable`).
- `similar_dissection_characterization` — FILLED (sorry removed) as an immediate,
  vacuous consequence (the `n ∉ {2,3,5}` hypothesis is unused). Documented as a
  model-artifact, not real geometry.
- `no_exceptional_similar_in_model (T) : CanDissectIntoSimilar T 2 ∧ … 3 ∧ … 5`
  — proves `exceptional_similar_cases` is model-FALSE (its direct refutation,
  similar analogue of `no_square_only_in_model`). `exceptional_similar_cases`
  retained as a model-false aspirational sorry, doc corrected.

## Why the (now 4) sorries can't be filled here
All four are *model-false* in the area+similarity model: `soifer_square_only`,
`integral_independence_implies_square_only`, `exceptional_similar_cases`,
`soifer_family_square_only`. They are genuine geometric statements awaiting a
faithful tiling predicate.

## Next directions
- Replace `CongruentDissection` AND `CanDissectIntoSimilar` with a faithful
  geometric tiling predicate (the open, hard core). Only then do these statements
  become *true* targets rather than model-artifacts.
- Do NOT add further area-compatibility lemmas pretending to be dissection
  progress. The model-inadequacy diagnosis is now COMPLETE for both predicates
  (congruent over-counts → `dissectionCounts_eq`/`no_square_only_in_model`;
  similar over-counts → `canDissectIntoSimilar_of_one_le`/`no_exceptional_similar_in_model`).

## Build note (2026-06-26)
Could not machine-verify: Docker build blocked by the persistent Mathlib-cache
`.ltar` Permission-denied error (cached path) / OOM at the ~7.65GB VM ceiling
(from-source path). New proofs mirror the already-verified `all_counts_achievable`
rewrite chain and use only standard Mathlib lemmas (`mul_div_mul_left`,
`Triangle.area_scale`, `Real.sq_sqrt`), all confirmed present in pinned Mathlib.

---
## (Prior) Session 2026-06-26 (researcher-3)
Turned the informal over-counting note into proved theorems (mirroring the already-verified `universal_square_dissection` / `equilateral_dissects_to_3`):
- `all_counts_achievable (T) (n) (hn : n ≥ 1) : CanDissectInto T n` — witness `T.scale (1/√n)`.
- `dissectionCounts_eq : DissectionCounts T = {n | 1 ≤ n}`.
- `not_isPerfectSquare_two : ¬ IsPerfectSquare 2`.
- `no_square_only_in_model (T) : ¬ HasSquareOnlyProperty T` (2 is achievable & non-square).
Added doc notes to `soifer_square_only` and `erdos_633` flagging they are model-false (refuted by `no_square_only_in_model`).
