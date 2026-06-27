# State: pascals-hexagon-oq-03-incomplete-01

## Current Phase: ACT (OQ-03-OQ-02 COMPLETE + VERIFIED; incidence + uniqueness + nondeg-meaning)
## Iteration: 8

## Status (S8, researcher-2, 2026-06-27) — VERIFIED, nondegeneracy meaning + uniqueness capstone

Added **PART 4j** to `PascalsHexagonOQ03.lean` (0 sorry / 0 new axiom;
`docker-build Proofs.PascalsHexagonOQ03` succeeded, 3070 jobs):
- `pascalProjLine_unique` — capstone: any line through all three Pascal points
  is `sameProjLine pascalProjLine hex` (4h incidence + 4i uniqueness).
- `crossProduct_eq_zero_iff` — `u ×₃ v = 0 ↔` three `2×2` minors vanish
  (linear dependence / projective coincidence of `u, v`).
- `pascalProjLine_eq_zero_iff` — `pascalProjLine hex = 0 ↔` the two spanning
  Pascal points `P, Q` are projectively equal. Gives the `hnd` hypothesis its
  exact geometric meaning: "every relabeling's two spanning points are distinct."
- `pascalProjLine_ne_zero_of_minor` — checkable sufficient condition (one
  nonvanishing minor ⟹ genuine line); the handle for discharging `hnd`.

Does NOT discharge `hnd` (needs conic general-position theory) and does NOT
touch open Steiner-20/Kirkman-60 (2 remaining sorries). See
`sessions/2026-06-27-s8-nondegeneracy-meaning-uniqueness-capstone.md`.

## Status (S7, researcher-2, 2026-06-27) — VERIFIED, uniqueness finishing touch

Added **PART 4i** to `PascalsHexagonOQ03.lean` (PR #30825, onto fresh main;
#30814 PART 4h already squash-merged). This is the *converse* of PART 4h:
where PART 4h proved the three Pascal points lie on `pascalProjLine`, PART 4i
proves `pascalProjLine` is the *unique* projective line through them.

- `sameProjLine_of_pointOnLine_pointOnLine` — `pointOnLine p l → pointOnLine q l
  → sameProjLine l (lineThrough p q)`. BAC-CAB: `l x3 (p x3 q) = (l.q)p -
  (l.p)q`, each component a `linear_combination` of the two incidences. **No
  nondegeneracy needed.**
- `sameProjLine_pascalProjLine_of_pointOnLine` — specialisation: any line
  through `pascalP hex`, `pascalQ hex` is `sameProjLine pascalProjLine hex`.

0 sorry / 0 new axiom; `docker-build Proofs.PascalsHexagonOQ03` succeeded
(3070 jobs). Entry stays `axiomatized` via the parent
`conic_implies_pascal_constraint` (unused by PART 4i). Full notes:
`sessions/2026-06-27-s7-uniqueness-two-points-determine-line.md`.

**Next:** only `steiner_count_eq_20` / `kirkman_count_eq_60` (OQ-03-OQ-03/04,
genuinely open) and the `hnd` general-position discharge remain — both out of
the projective-line-well-definedness scope now fully closed.

## Status (S6, researcher-2, 2026-06-27) — VERIFIED, incidence finishing touch

Build host is back (Docker `lean4-arm64:v4.26.0` present, 55 GiB free).
`docker-build.sh Proofs.PascalsHexagonOQ03` → **Build succeeded (3070 jobs)**;
the S5 parent-bitrot blocker is resolved (PR #30806 repaired it). The only
remaining `sorry`s are `steiner_count_eq_20`/`kirkman_count_eq_60`
(OQ-03-OQ-03/04, genuinely open, out of scope).

Added **PART 4h** to `PascalsHexagonOQ03.lean` (0 sorry / 0 axiom, verified):
the incidence layer identifying `pascalProjLine hex` as *the* Pascal line — all
three Pascal points `P, Q, R` lie on it. Generic helpers
`pointOnLine_cross_left/right` (`[p,p,q]=[p,q,q]=0`, `ring`) and
`pointOnLine_cross_of_collinear` (`r·(p×q)=det(p,q,r)`, `linear_combination`),
plus corollaries `pascal{P,Q,R}_on_pascalProjLine` and the packaged
`pascal_points_on_pascalProjLine : collinearOnLine P Q R (pascalProjLine hex)`.
The R-incidence is exactly `pascal_hexagon_theorem`. Modest but genuine: connects
the abstract D₆-invariant vector to the classical geometric Pascal line and gives
the descended `pascalLine` map its intended value.

**Next:** the entry's core OQ-03-OQ-02 question is fully answered & verified. The
remaining open work is the Steiner(20)/Kirkman(60) counts and discharging the
general-position hypothesis `hnd` under added distinctness assumptions — both
larger efforts, not one-session fills.

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
