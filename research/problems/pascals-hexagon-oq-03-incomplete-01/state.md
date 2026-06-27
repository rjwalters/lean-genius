# State: pascals-hexagon-oq-03-incomplete-01

## Current Phase: ACT (math COMPLETE for OQ-03-OQ-02; verification BLOCKED on parent bitrot)
## Iteration: 5

## Status (S5, researcher-3, 2026-06-27) — VERIFICATION BLOCKER

OQ-03-OQ-02 (Pascal-line well-definedness) is **mathematically complete**: PART 4g
of `PascalsHexagonOQ03.lean` (`pascalProjLine_sameProjLine_of_mem` +
`…_of_mem_mem`, merged via PR #30630) closes it with a full
`Subgroup.closure_induction` over `hexagonalGroup`. Remaining OQ03 `sorry`s are
`steiner_count_eq_20` / `kirkman_count_eq_60` (OQ-03-OQ-03/04) — genuinely open,
out of scope.

**The entry cannot be machine-verified**: the parent `proofs/Proofs/PascalsHexagon.lean`
does not compile under the pinned Mathlib (v4.26.0). `PascalsHexagonOQ03.lean`
imports `Proofs.PascalsHexagon`, so the whole Pascal family is build-blocked.

This session offline-built the parent (shared olean cache; Docker still corrupt)
and found two layers:
- **Layer 1 (FIXED, this PR):** two `/-- … -/` docstrings placed *before*
  `set_option … in` — a v4.26.0 parse error. Moved `set_option` above the docstring
  for `pascal_std_conic_parametrized` and `crossProduct_projTransform`. Verified:
  **0 parse errors** remain. The broken syntax dates to #22746 (predates the Mathlib
  pin) ⇒ the file was merged build-pending and likely **never compiled** under
  v4.26.0; treat its `meta.json` verified claim as suspect.
- **Layer 2 (NOT fixed — Mechanic-scale):** 35 genuine Mathlib-drift proof failures
  remain (21 `simp` made-no-progress/timeout from Matrix `cons_val`/`det_fin_three`
  normal-form change; 7 `linarith`/`nlinarith`; 4 `unsolved goals` on the big `ring`
  identities; 2 type mismatches). ~30 distinct proofs across several failure modes;
  a partial fix gives no verification benefit (module only compiles once *all* are
  fixed). Full breakdown + line numbers in
  `sessions/2026-06-27-s5-parent-bitrot-blocker.md`.

**Next:** Mechanic repairs `PascalsHexagon.lean` (start with the replicable
simp-drift cluster, then the hard `ring` identities). Auditor flags the family's
meta verification status. Only after the family builds green is the optional
`pascalLine_sameProjLine_of_rep` capstone worth adding.

## Status (S4, researcher-6, 2026-06-27)
S4 added **PART 4e** to `PascalsHexagonOQ03.lean`: the *equivalence-relation*
(PER) structure for `sameProjLine`, which is the algebraic engine the quotient
descent (S3's "Next Action 2") consumes. New lemmas (0 sorry / 0 axiom, append
onto **PR #30630**):
- `sameProjLine_symm : l ∥ m → m ∥ l` (cross-product anti-symmetry; coordinate
  proof, three `linear_combination -hᵢ`).
- `sameProjLine_trans : m ≠ 0 → l ∥ m → m ∥ n → l ∥ n` — the real linear-algebra
  content. For each coordinate `k`, `m k • (l ×₃ n) = 0` via a fixed
  `linear_combination` of the components of `l ×₃ m` and `m ×₃ n` (all 9
  coefficient certificates derived by hand and recorded in the source). Then
  `m ≠ 0` picks a nonzero coordinate and `smul_eq_zero` finishes. The `m ≠ 0`
  hypothesis is necessary (the zero vector is parallel to everything).
- `sameProjLine_isPER` — bundles refl + symm + (nonzero-middle) trans.
- `pascalLine_hexRot_hexRev_sameProjLine` — first PER application: rot-line and
  rev-line are the *same* projective line as each other (given the base Pascal
  line is nonzero), the exact shape each closure-induction step takes.

**Build STILL BLOCKED** (host Data volume 100% full / 5.3 GiB; Docker
containerd blob store I/O-corrupt — `docker system df` errors; 9 zombie
`lean-build-*` containers hung; Aristotle MCP returns "Resource not found").
PART 4e proofs reuse only the file's existing `cross_apply` simp set +
`linear_combination` and standard `smul_eq_zero`/`Function.ne_iff`; the 9
transitivity certificates were verified by hand algebra. Same verification
status as the rest of PR #30630.

## Status (S3, researcher-6, 2026-06-27)
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
   (a) the index-2 `![…]` reduction in the new `linear_combination` goals
   (same `cross_apply` simp set as PART 4d, so it succeeds/fails together);
   (b) `smul_eq_zero` instance resolution `NoZeroSMulDivisors ℝ (Fin 3 → ℝ)`
   (standard, expected fine); (c) any `linear_combination` certificate with a
   sign error — all 9 re-derivable from the comment in PART 4e.
2. **Full quotient descent** (remaining gap, now *unblocked algebraically* by
   PART 4e): `sameProjLine` is reflexive + symmetric + transitive-along-nonzero,
   so a `Subgroup.closure_induction` over `{hexRot, hexRev}` propagates
   generator-invariance to all of `hexagonalGroup`. Two sub-tasks left:
   (i) a `permuteHexagon hex (g*h) = permuteHexagon (permuteHexagon hex g) h`
   composition lemma so the inductive step chains two generator-invariances via
   `sameProjLine_trans`; (ii) the non-degeneracy lemma `lineThrough (pascalP
   hex) (pascalQ hex) ≠ 0` (Pascal points distinct on a non-degenerate conic)
   to discharge the `m ≠ 0` side-condition uniformly. Then relate
   `permuteHexagon hex g` to `pascalLine`'s `lbl.out'` representative for genuine
   `Quotient`-level well-definedness of `pascalLine`.

## Out of scope
`steiner_count_eq_20`, `kirkman_count_eq_60` (OQ-03-OQ-03/04) — genuinely open
(Conway–Ryba concurrence combinatorics).
