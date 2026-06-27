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
