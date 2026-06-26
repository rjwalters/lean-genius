# Erdős #633 — Square-Only Triangle Dissections (knowledge)

## State
- OPEN ($25). Gallery file `proofs/Proofs/Erdos633Problem.lean`, badge `wip`, 5 real sorries.
- Model: `CongruentDissection` encodes ONLY area-compatibility (`area T = n·area S`) + side-ratio similarity. It does NOT encode a real tiling.

## Key structural fact (CRITICAL)
The model **over-counts**: by `Triangle.area_scale`, the scaled copy `T.scale (1/√n)` satisfies both numeric conditions for *every* `n ≥ 1`. Hence `DissectionCounts T = {n | n ≥ 1}` for every triangle, so the square-only direction is **model-false**, not just unproved.

## Session 2026-06-26 (researcher-3)
Turned the informal over-counting note into proved theorems (mirroring the already-verified `universal_square_dissection` / `equilateral_dissects_to_3`):
- `all_counts_achievable (T) (n) (hn : n ≥ 1) : CanDissectInto T n` — witness `T.scale (1/√n)`.
- `dissectionCounts_eq : DissectionCounts T = {n | 1 ≤ n}`.
- `not_isPerfectSquare_two : ¬ IsPerfectSquare 2`.
- `no_square_only_in_model (T) : ¬ HasSquareOnlyProperty T` (2 is achievable & non-square).
Added doc notes to `soifer_square_only` and `erdos_633` flagging they are model-false (refuted by `no_square_only_in_model`).

## Why the 5 sorries can't be filled here
`soifer_square_only`, `soifer_family_square_only`, `integral_independence_implies_square_only` are model-false. The two `CanDissectIntoSimilar` sorries (`similar_dissection_characterization`, `exceptional_similar_cases`) are the hard #634 content.

## Next directions
- Replace `CongruentDissection` with a faithful geometric tiling predicate (the open, hard core). Only then do the square-only statements become *true* targets.
- Do NOT keep adding lemmas on top of the over-counting model — they are area-compatibility facts, not dissection facts.

## Build note
Could not machine-verify this session: Docker daemon was not running in the worktree (`docker-build.sh` → "Docker daemon is not running"). New proofs are copies of verified tactic patterns already in the file.
