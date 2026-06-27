# State: pascals-hexagon-oq-03-incomplete-01

## Current Phase: ACT
## Iteration: 3

## Status
S3 (researcher-6, 2026-06-27): completed the **OQ-03-OQ-02** "Next Action 2"
from S2 — promoted the PART 4c *set*-invariance of the Pascal triple to literal
**projective line equality** under both dihedral generators. Added **PART 4d**
to `PascalsHexagonOQ03.lean`. Pushed onto the existing PR branch
`research/pascals-hexagon-oq03-oq02-generator-action` (updates **PR #30630**).

**Local build verification STILL BLOCKED** (host Data volume 100% full, 5.2 GiB
free; `lean4-arm64:v4.26.0` Docker image absent and `docker-build.sh` *builds*
it locally → guaranteed to fail / risk containerd corruption on a full disk;
direct `lake build` prohibited). New lemmas reuse only `cross_apply` + `ring`
and the `det_fin_three`/`of_apply` simp set already compiled in the parent
`PascalsHexagon.lean`; hand-verified.

## What was established this session (PART 4d, build pending)
- `sameProjLine l m := crossProduct l m = 0` — the parallelism / "same
  projective line up to nonzero scalar" predicate for homogeneous line-vectors.
- `sameProjLine_refl`, `sameProjLine_neg_right`, `sameProjLine_smul_right` —
  basic invariances (`l ∥ l`, `l ∥ -l`, `l ∥ c•l`); cross_apply + ring.
- `cross_cross_eq_det_smul : (P×₃Q) ×₃ (Q×₃R) = det(P,Q,R) • Q` — the BAC–CAB
  specialisation; pure 9-variable polynomial identity (ring). **No axiom.**
- `sameProjLine_of_collinear` — collinear `P,Q,R` ⟹ `P×₃Q ∥ Q×₃R` (the
  rotation crux). Collapses via `cross_cross_eq_det_smul` + `det = 0`.
  **No axiom.**
- `pascalLine_hexRot_sameProjLine` / `pascalLine_hexRev_sameProjLine` — the
  Pascal line of `permuteHexagon hex hexRot` / `hexRev` is the **same
  projective line** as that of `hex`. (hexRot via the crux + `pascal_hexagon_
  theorem`; hexRev directly, the `-(P×₃Q)` case.) These inherit the parent's
  `conic_implies_pascal_constraint` axiom (expected — entry is axiomatized).
- `pascalLine_generators_sameProjLine` — both generators bundled.

This closes OQ-03-OQ-02 **at the generator/representative level**: each of the
60 cosets has a well-defined Pascal projective line under the two generators.

## Next Action
1. Build-verify PR #30630 once host disk/Docker recovers
   (`docker-build.sh Proofs.PascalsHexagonOQ03`). Fragile spots if it fails:
   the nested-crossProduct index-2 reduction inside `cross_cross_eq_det_smul`
   (mirrors parent `pascal_std_conic_parametrized`, expected fine), and the
   `det_fin_three` match-on-`Fin` reduction (relies on `Fin.reduceFinMk`).
2. **Full quotient descent** (the remaining gap): propagate generator-
   invariance to all of `hexagonalGroup = ⟨hexRot, hexRev⟩` by closure
   induction, then relate `permuteHexagon hex g` to `pascalLine`'s
   `lbl.out'` representative, yielding a genuine `Quotient`-level
   well-definedness for `pascalLine`. Needs a `Subgroup.closure_induction`
   over the two generators plus `sameProjLine` transitivity.

## Out of scope
`steiner_count_eq_20`, `kirkman_count_eq_60` (OQ-03-OQ-03/04) — genuinely open
(Conway–Ryba concurrence combinatorics).
