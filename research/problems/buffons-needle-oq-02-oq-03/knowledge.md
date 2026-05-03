# buffons-needle-oq-02-oq-03: Cauchy-Crofton Formula for Arbitrary Measures on S^{n-1}

**Status**: COMPLETED (2026-05-03)
**Gallery entry**: `src/data/proofs/buffons-needle-oq-02-oq-03/`
**Lean file**: `proofs/Proofs/BuffonsNeedleOQ02OQ03.lean`
**Stats**: 255 lines, 2 axioms, 0 sorries, 12 theorems

---

## Session 2026-05-03 (Session 1) — Initial formalization + gallery entry

**Mode**: FRESH
**Outcome**: completed

### What I Did

1. Identified buffons-needle-oq-02-oq-03 as a fresh, tractable problem absent from the gallery
2. Created `proofs/Proofs/BuffonsNeedleOQ02OQ03.lean` with the full Cauchy-Crofton framework:
   - **Part I**: Hyperplane/Segment structures and crossing predicate
   - **Part II**: Crossing measure lemma (PROVED) — Lebesgue measure of {t : H(u,t) crosses [A,B]} = |⟪u,B-A⟫| via `Real.volume_Icc` + `max_sub_min_eq_abs`
   - **Part III**: crossingIntegral definition and Fubini axiom
   - **Part IV**: Linearity lemmas (smul, symm, polygonal noodle theorem) — all proved
   - **Part V**: alpha function (α₁=1, α₂=2/π, α₃=1/2) and isotropy axiom
   - **Part VI**: Classical 2D/3D consistency, alpha_decreasing by norm_num
3. Added import to `proofs/Proofs.lean`
4. Created gallery entry at `src/data/proofs/buffons-needle-oq-02-oq-03/meta.json`
5. Created research JSON at `src/data/research/problems/buffons-needle-oq-02-oq-03.json`

### Key Findings

- The crossing measure lemma is the mathematical core and was fully provable in Lean
- `Real.volume_Icc (min_le_max _ _)` + `max_sub_min_eq_abs` gives the interval length as |max - min| = |u·B - u·A|
- `inner_sub_right` reduces |⟪u,B-A⟫| to |u·B - u·A| via abs_sub_comm
- Fubini exchange needs measurability of crossing_count — non-trivial, correctly axiomatized
- Isotropy needs O(n) Haar measure change-of-variables — non-trivial, correctly axiomatized
- All linearity consequences (smul, symm, polygonal) follow from `inner_smul_right`, `inner_neg_right`, etc.

### Axiom Assessment

| Axiom | Classification | Notes |
|-------|----------------|-------|
| `cauchy_crofton_fubini` | HARD | Standard Fubini-Tonelli; blocked by measurability of crossing_count |
| `isotropy_yields_alpha` | HARD | Needs O(n) Haar measure + change-of-variables |

Both are HARD (formalization of known mathematics), not OPEN. Aristotle candidate if infrastructure exists.

### Next Steps

- Attempt `cauchy_crofton_fubini` via `MeasureTheory.lintegral_prod` (Fubini for ENNReal integrals)
- Attempt `isotropy_yields_alpha` via O(n) group action and Haar measure uniqueness in Mathlib
- If both proved: 0 axioms, 0 sorries — fully verified
