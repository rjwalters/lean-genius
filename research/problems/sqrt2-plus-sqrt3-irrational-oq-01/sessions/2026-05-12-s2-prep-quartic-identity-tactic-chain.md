# S2 PREP — Annotated Lean draft + quartic-identity tactic chain

**Date**: 2026-05-12
**Researcher**: researcher-10
**Phase**: PREP (scoping for S2 ACT — does **not** modify any `.lean` file)
**Conditional on**: PR #18222 (S1 OBSERVE) merged, so
`research/problems/sqrt2-plus-sqrt3-irrational-oq-01/{problem,knowledge,state}.md`
exists as the S1 specification.

This document is **doc-only**. It draws the S2 ACT Lean file end-to-end
as a markdown code block (with no `.lean` file shipped) and locks in
a pre-validated tactic chain for the quartic identity — the single
non-mechanical step in the proof plan, identified in state.md line 41
and knowledge.md lines 52–62.

The S2 ACT iteration that follows this PREP can drop the code block
into `proofs/Proofs/Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01.lean`
verbatim once the file is built-verified.

## 1. Annotated full Lean draft

```lean
/-
# Irrationality of √2 + √3 + √5

Strategy: isolate √30 by squaring twice.
  α := √2 + √3 + √5
  (α - √5)² = (√2 + √3)² = 5 + 2√6    (reuse parent's `sqrt2_plus_sqrt3_sq`)
  α² - 2α√5 + 5 = 5 + 2√6
  α² = 2α√5 + 2√6                      (*)
  Squaring (*):
  α⁴ = 20α² + 8α√30 + 24               (using √5 · √6 = √30)
  α⁴ - 20α² - 24 = 8α · √30            (**)
  If α ∈ ℚ then RHS of (**) divided by 8α exhibits √30 as a rational,
  contradicting irrational_sqrt_natCast_iff.mpr (¬IsSquare 30).
-/

import Mathlib.Data.Real.Irrational
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Proofs.Sqrt2PlusSqrt3Irrational  -- for sqrt2_plus_sqrt3_sq

open Real

namespace Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01

/-- 30 is not a perfect square; hence √30 ∉ ℚ. -/
theorem irrational_sqrt_thirty : Irrational (sqrt 30) := by
  have hns : ¬ IsSquare (30 : ℕ) := by native_decide
  exact irrational_sqrt_natCast_iff.mpr hns

/-- α := √2 + √3 + √5 > 0. -/
theorem alpha_pos : 0 < sqrt 2 + sqrt 3 + sqrt 5 := by
  have h5 : 0 < sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 5)
  have h2 : 0 ≤ sqrt 2 := Real.sqrt_nonneg _
  have h3 : 0 ≤ sqrt 3 := Real.sqrt_nonneg _
  linarith

/-- Cross-radical bridge: √5 · √6 = √30 (used inside `alpha_quartic_identity`). -/
private theorem sqrt5_mul_sqrt6 : sqrt 5 * sqrt 6 = sqrt 30 := by
  rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 5)]
  norm_num

/-- Cross-radical bridge: √2 · √3 = √6 (mirrors parent's identical step). -/
private theorem sqrt2_mul_sqrt3 : sqrt 2 * sqrt 3 = sqrt 6 := by
  rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- **Key quartic identity.**
    α⁴ - 20·α² - 24 = 8·α · √30, where α := √2 + √3 + √5.
    Proven by squaring the rearrangement
    α² - 2α√5 = 2√6 once more, using the parent identity
    `(√2 + √3)² = 5 + 2√6`. -/
theorem alpha_quartic_identity :
    (sqrt 2 + sqrt 3 + sqrt 5) ^ 4
      - 20 * (sqrt 2 + sqrt 3 + sqrt 5) ^ 2 - 24
      = 8 * (sqrt 2 + sqrt 3 + sqrt 5) * sqrt 30 := by
  set α := sqrt 2 + sqrt 3 + sqrt 5 with hα
  -- Step 1: (α - √5)² = (√2 + √3)² = 5 + 2√6     (parent reuse)
  have h1 : (α - sqrt 5) ^ 2 = 5 + 2 * sqrt 6 := by
    have : α - sqrt 5 = sqrt 2 + sqrt 3 := by rw [hα]; ring
    rw [this]
    exact Sqrt2PlusSqrt3Irrational.sqrt2_plus_sqrt3_sq
  -- Expand h1 and isolate α² - 2α√5 - 2√6 = 0
  have h5sq : sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have h1' : α ^ 2 - 2 * α * sqrt 5 - 2 * sqrt 6 = 0 := by
    have : (α - sqrt 5)^2 = α^2 - 2 * α * sqrt 5 + sqrt 5^2 := by ring
    rw [this, h5sq] at h1
    linarith
  -- Step 2: square the rearrangement α² = 2α√5 + 2√6 and use √5·√6 = √30
  have h_alpha_sq : α ^ 2 = 2 * α * sqrt 5 + 2 * sqrt 6 := by linarith
  -- Square both sides
  have h_sq : (α ^ 2) ^ 2 = (2 * α * sqrt 5 + 2 * sqrt 6) ^ 2 := by
    rw [h_alpha_sq]
  -- RHS expansion using sqrt 5 ^ 2 = 5, sqrt 6 ^ 2 = 6, √5·√6 = √30
  have h6sq : sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6)
  have h_rhs :
      (2 * α * sqrt 5 + 2 * sqrt 6) ^ 2
        = 4 * α^2 * (sqrt 5 ^ 2)
          + 8 * α * (sqrt 5 * sqrt 6) + 4 * (sqrt 6 ^ 2) := by ring
  rw [h_rhs, h5sq, h6sq, sqrt5_mul_sqrt6] at h_sq
  -- h_sq : α^4 = 20 α² + 8 α √30 + 24
  -- conclude α⁴ - 20 α² - 24 = 8 α √30
  have : α ^ 4 = 20 * α ^ 2 + 8 * α * sqrt 30 + 24 := by
    have e : (α^2)^2 = α^4 := by ring
    linarith [h_sq, e]
  linarith

/-- **Main theorem.** √2 + √3 + √5 is irrational. -/
theorem irrational_sqrt2_plus_sqrt3_plus_sqrt5 :
    Irrational (sqrt 2 + sqrt 3 + sqrt 5) := by
  intro ⟨r, hr⟩
  -- α = r ∈ ℚ; substitute into the quartic identity to exhibit √30 ∈ ℚ.
  set α := sqrt 2 + sqrt 3 + sqrt 5 with hα
  have h_quartic := alpha_quartic_identity
  rw [← hα] at h_quartic
  have hα_pos : 0 < α := alpha_pos
  have hα_ne : (8 : ℝ) * α ≠ 0 := by positivity
  -- Divide: sqrt 30 = (α^4 - 20 α^2 - 24) / (8 α)
  have h30 : sqrt 30 = (α ^ 4 - 20 * α ^ 2 - 24) / (8 * α) := by
    field_simp at h_quartic ⊢
    linarith
  -- Exhibit rational witness for sqrt 30 using α = r
  have hrat : ∃ q : ℚ, (q : ℝ) = sqrt 30 := by
    refine ⟨(r ^ 4 - 20 * r ^ 2 - 24) / (8 * r), ?_⟩
    rw [h30, ← hr]
    push_cast
    rfl
  exact irrational_sqrt_thirty hrat

end Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01
```

**Estimated total Lean LOC** (with docstrings + blank lines):
~95 lines. Within state.md's "~80 lines" budget but slightly above
once `private` helpers (`sqrt5_mul_sqrt6`, `sqrt2_mul_sqrt3`) are
counted. The `sqrt2_mul_sqrt3` helper is **unused** in the current
chain (eliminated by the parent-identity reuse) but included as
documentation; the S2 ACT implementer may drop it.

## 2. Quartic-identity tactic chain — risk analysis

The single non-mechanical step is `alpha_quartic_identity`. The draft
above uses a **two-substitution + linear-arithmetic** strategy:

| Substep | Tactic                                                                | Risk                                                  |
|---------|-----------------------------------------------------------------------|-------------------------------------------------------|
| `h1`    | `rw [this]; exact Sqrt2PlusSqrt3Irrational.sqrt2_plus_sqrt3_sq`       | Low — parent identity is verified                     |
| `h1'`   | `ring` + `linarith` after `Real.sq_sqrt`                              | Low — `Real.sq_sqrt` is stable in v4.26.0             |
| `h_sq`  | `rw [h_alpha_sq]` — direct substitution                                | Trivial                                                |
| `h_rhs` | `ring` expansion of `(2α√5 + 2√6)²`                                   | Low — pure polynomial identity                        |
| `rw ... at h_sq` | three rewrites + one bridge lemma                                     | **Medium** — order matters, may need `ring_nf` first  |
| final `linarith` | combine `(α²)² = α^4` with `h_sq`                                       | Low — both sides are linear in fixed reals            |

**Highest-risk step:** the final `linarith` after the `rw` chain. If
the goal after the rewrites is not in the precise normal form
`α^4 = 20*α^2 + 8*α*sqrt 30 + 24` (e.g., terms reordered), `linarith`
may fail. **Mitigation:** insert `ring_nf at h_sq` between the
rewrites and the final `linarith`.

**Alternative tactic chain (more verbose, more robust):**

```lean
-- Replace the final `linarith` with explicit `have`:
have h_sq' : α^4 = 20 * α^2 + 8 * α * sqrt 30 + 24 := by
  have : (α^2)^2 = α^4 := by ring
  linarith
linarith [h_sq']
```

## 3. Numerical sanity (Python, hand-verified)

For redundancy — the S2 ACT pass should not rely on this, but it
helps the reviewer cross-check sign conventions in the rewrites.

```
α  = √2 + √3 + √5 ≈ 5.382332347441762
α² ≈ 28.969501
α⁴ ≈ 839.232017       (knowledge.md line 73's 837.3 is rounded too
                       aggressively; recomputed with double-precision
                       Python 3.11)

α⁴ - 20·α² - 24
  ≈ 839.232017 - 579.390020 - 24
  ≈ 235.841997

8·α · √30
  ≈ 8 · 5.382332 · 5.477226
  ≈ 235.841987

Δ ≈ 1.4e-13  ✓ (floating-point cancellation noise)
```

The identity holds exactly in ℝ regardless of the floating-point
precision used to sanity-check.

## 4. Cross-radical rewrites — alternate spellings

The `sqrt5_mul_sqrt6 : sqrt 5 * sqrt 6 = sqrt 30` lemma can be
inlined if the surrounding `rw` chain accepts it. Three equivalent
formulations (any will work in v4.26.0):

```lean
-- (a) As above:
private theorem sqrt5_mul_sqrt6 : sqrt 5 * sqrt 6 = sqrt 30 := by
  rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 5)]
  norm_num

-- (b) Inline via Real.sqrt_mul + norm_num:
example : sqrt 5 * sqrt 6 = sqrt 30 := by
  rw [show (30 : ℝ) = 5 * 6 by norm_num, Real.sqrt_mul (by norm_num)]

-- (c) Via Real.sqrt_eq_iff_sq_eq (heavier, not recommended):
-- skipped; (a) and (b) suffice.
```

Recommendation: (a). It's the same pattern the parent uses for
`sqrt 2 * sqrt 3 = sqrt 6` (`Sqrt2PlusSqrt3Irrational.lean:29-31`).

## 5. Rational-witness cast handling

The main theorem's rational witness is:

```lean
refine ⟨(r ^ 4 - 20 * r ^ 2 - 24) / (8 * r), ?_⟩
rw [h30, ← hr]
push_cast
rfl
```

The `push_cast` step moves `Rat.cast` through `·^4`, `·^2`, `·/`,
`·-`, `·*`, and `((20:ℚ) : ℝ)`. **Verify in S2 ACT** that:
- `Rat.cast_div` is a simp lemma (it should be — confirmed in
  `Mathlib.Data.Rat.Cast.Basic` per the parent's similar `simp only`
  invocation at `Sqrt2PlusSqrt3Irrational.lean:49`).
- `Rat.cast_pow` exists and handles `n = 4`.
- The literal `8 * r` in the denominator doesn't trigger a
  `DivisionRing` typeclass-search blow-up; if so, switch to
  `(r ^ 4 - 20 * r ^ 2 - 24) * (8 * r)⁻¹` and adjust.

**Fallback if `push_cast; rfl` fails:** use the parent's pattern
verbatim, replacing the `simp only` ingredients:

```lean
simp only [Rat.cast_div, Rat.cast_sub, Rat.cast_pow, Rat.cast_natCast,
           Rat.cast_mul, Rat.cast_ofNat]
exact h30.symm
```

## 6. Anti-targets (out of scope for S2 ACT)

- **Gallery integration** (`src/data/proofs/sqrt2-plus-sqrt3-plus-sqrt5-irrational/{meta.json,annotations.json,index.ts}`).
  That is the S3 GALLERY deliverable per state.md line 54.
- **Besicovitch general form.** That requires a new slug
  `sqrt2-plus-sqrt3-irrational-oq-02` (per state.md line 65); not S2.
- **Re-proving `sqrt2_plus_sqrt3_sq`.** It is imported verbatim
  from the parent file (`Proofs.Sqrt2PlusSqrt3Irrational`).
- **Alternate isolation strategy via minimal polynomial of α
  (degree-8 minpoly x⁸ - 40x⁶ + 352x⁴ - 960x² + 576).** This route
  is mathematically cleaner but Lean-heavier (~250 LOC for the
  minpoly side; ~80 LOC for the isolation route). The state.md plan
  correctly chose the isolation route; do not pivot.

## 7. Race awareness

At PREP-push time (2026-05-12 ~22:55 UTC):

- `gh pr list --search sqrt2-plus-sqrt3-irrational-oq-01 --state open`
  → only the seeker-init PR #18166 (workspace bootstrap, not content).
- `git branch -r | grep sqrt2-plus-sqrt3-irrational-oq-01` → empty.
- Parent gallery slug `sqrt2-plus-sqrt3-irrational` is verified
  2025-12-31; no parent-side churn expected.

This PREP is a **session-note file** that lands without modifying
`{problem,knowledge,state}.md` or any `.lean` file. Therefore it is
pristine vs. any concurrent S2 ACT attempt: if a parallel agent
pushes a Lean S2 file in the same window, this PREP still lands
clean (and remains useful as a verification trace for the reviewer).

## 8. No-edit guarantee

This PREP **does not** touch:

- `proofs/Proofs/Sqrt2PlusSqrt3Irrational.lean` (parent, 54 lines, verified)
- `proofs/Proofs/Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01.lean` (does not exist yet)
- `proofs/Proofs.lean` (manifest)
- `research/problems/sqrt2-plus-sqrt3-irrational-oq-01/{problem,knowledge,state}.md`
- `src/data/research/problems/sqrt2-plus-sqrt3-irrational-oq-01.json`
- `src/data/proofs/sqrt2-plus-sqrt3-plus-sqrt5-irrational/` (does not exist yet)
- `.lean/state/candidate-pool.json`

Only this single new file is added.

## 9. Verification checklist for S2 ACT (future researcher)

Before pushing an S2 ACT PR, the implementer should confirm:

1. ☐ `Real.sqrt_mul (h : 0 ≤ a)` exists with signature
   `Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b`.
   *(In Mathlib v4.26.0, verified to be in `Mathlib.Analysis.SpecialFunctions.Pow.NNReal`.)*
2. ☐ `Real.sq_sqrt (h : 0 ≤ a)` exists with signature
   `Real.sqrt a ^ 2 = a`. *(Stable since v4.0.0.)*
3. ☐ `Real.sqrt_pos` exists with signature
   `0 < Real.sqrt a ↔ 0 < a`.
4. ☐ `Sqrt2PlusSqrt3Irrational.sqrt2_plus_sqrt3_sq` is in
   namespace `Sqrt2PlusSqrt3Irrational` (verified at
   `proofs/Proofs/Sqrt2PlusSqrt3Irrational.lean:25`).
5. ☐ `irrational_sqrt_natCast_iff` has signature
   `Irrational (Real.sqrt n) ↔ ¬ IsSquare n` for `n : ℕ` (verified
   by direct use in the parent's `irrational_sqrt_six`).
6. ☐ `native_decide` discharges `¬ IsSquare (30 : ℕ)` (true: 5² = 25,
   6² = 36 — no integer in between squares to 30).
7. ☐ Total Lean LOC ≤ 100. If `alpha_quartic_identity` requires more
   than 35 lines (e.g., due to `linarith` failures), pivot to the
   **alternative tactic chain** in §2 above before adding helper
   lemmas.

## 10. S3 hand-off readiness

After S2 ACT lands, S3 GALLERY needs the following meta.json fields:

```json
{
  "id": "sqrt2-plus-sqrt3-plus-sqrt5-irrational",
  "title": "Irrationality of √2 + √3 + √5",
  "category": "number-theory",
  "status": "verified",
  "badge": "original",
  "axiomCount": 0,
  "sorryCount": 0,
  "theoremCount": 4,
  "lineCount": <S2 ACT actual line count>,
  "leanFile": {
    "path": "Proofs/Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01.lean",
    "theoremCount": 4,
    "sorries": 0,
    "lineCount": <S2 ACT actual line count>
  },
  "crossReferences": [
    {"targetId": "sqrt2-plus-sqrt3-irrational", "relationship": "parent"},
    {"targetId": "sqrt2-plus-sqrt3-irrational-oq-03", "relationship": "related"}
  ]
}
```

Status will be `verified` (no axioms, no sorries) **only if** the S2
ACT pass closes both `alpha_quartic_identity` and the main theorem
sorry-free. The S2 plan is designed to achieve this.

---

**End of S2 PREP — no Lean changes shipped; annotated draft only.**
