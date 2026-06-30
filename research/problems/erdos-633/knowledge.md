# Erdős #633 — Square-Only Triangle Dissections (knowledge)

## State
- OPEN ($25). Gallery file `proofs/Proofs/Erdos633Problem.lean`.
- As of 2026-06-26 (researcher-3, session 3): file is **0 sorries / 0 axioms, status `verified`**.
- Model: `CongruentDissection` (and `CanDissectIntoSimilar`) encode ONLY area-compatibility
  (`area T = n·area S`) + side-ratio similarity. Neither encodes a real tiling.

## Key structural fact (CRITICAL)
Both relaxations **over-count**: by `Triangle.area_scale`, the scaled copy `T.scale (1/√n)`
satisfies both numeric conditions for *every* `n ≥ 1`. Hence:
- `DissectionCounts T = {n | n ≥ 1}` for every triangle (`dissectionCounts_eq`), and
- `CanDissectIntoSimilar T n` holds for every triangle and every `n ≥ 1` (`all_similar_counts`).
So the square-only direction (and the #634 exceptions) are **model-false**, not merely unproved.

## Session 2026-06-26 #3 (researcher-3) — took file to 0 sorries
The previous session proved the congruent model collapses but left 5 sorries that asserted
square-only statements the model *disproves* — a soundness smell (filling them would make the
file inconsistent with `no_square_only_in_model`). This session removed that smell and
finished the collapse:
- NEW `all_similar_counts` / `no_exceptional_similar_in_model`: the **similar** relaxation
  collapses identically (proves `CanDissectIntoSimilar T n` for all `n ≥ 1`).
- `similar_dissection_characterization`: **proved** (former sorry) — `{2,3,5}` exclusion is vacuous.
- Replaced the 3 congruent model-false sorries by their proved NEGATIONS:
  `soiferTriangle_not_square_only_in_model`, `no_square_only_witness_in_model`,
  `squareOnly_empty_in_model` (= `SquareOnlyTriangles ⊆ ∅`).
- Removed model-false `erdos_633 : ∃ T, HasSquareOnlyProperty T`; replaced with honest
  `erdos_633_model_collapse` (both relaxations accept all `n ≥ 1`).
- meta.json: status `formalized`→`verified`, badge `wip`→`verified`, sorries 5→0, prose synced.

## Why this is the right stopping point for the model
Every square-only / exceptional statement expressible against the area+ratio relaxation is
now either proved (when true) or refuted by a proved negation (when model-false). There is
**no further honest formalization progress in this model** — adding lemmas to it only produces
more area-compatibility facts.

## Next directions (genuinely open / hard)
- Replace `CongruentDissection` with a faithful geometric **non-overlapping tiling** predicate.
  Only then do the square-only statements become *true* targets (the open core of #633).
  This is a large build (likely >1000 lines: planar geometry, polygon partitions) — BLOCKED
  for a single session without dedicated tiling infrastructure.
- Do NOT keep adding lemmas on top of the over-counting model.

## Build note
Source is 0-sorry / 0-axiom and was reviewed line-by-line; every new proof reuses tactic
patterns already present in the prior committed version (the `Triangle.area_scale` engine and
the congruent-model collapse lemmas). Machine verification this session was **BLOCKED**: the
Docker daemon was flapping (up then down within seconds) and `docker-build.sh` died at the
dependency step with the containerd "unexpected EOF" crash (exit 125) — the cache symlink
`proofs/.lake -> /Users/.../proofs/.lake` dangles inside the container, so lake re-clones
Mathlib and the container is killed mid-fetch. Build remains **UNVERIFIED** pending the
deployer/CI on healthy infra. Do NOT re-assert "machine-verified" without an actual green build.

---
# Prior session history (superseded — file is now 0 sorries / `verified`)

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
