import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import Proofs.CramersRuleOQ01OQ02
import Proofs.CramersRuleOQ01OQ02OQ01

/-
# Inductive n×n Quasideterminant Theory
# (cramers-rule-oq-01-oq-02-oq-01-oq-01)

S2 — Route A (commutative): uniform-in-n quasideterminant `qdetF` over a field.
S3 — Route B SCAFFOLD (non-commutative): one-step Schur formula
`qdetN_step` plus field-consistency reduction to `qdetF` (deferred sorry).

This file extends the 2×2 / 3×3 Gelfand–Retakh quasideterminant theory
(`CramersRuleOQ01OQ02`, `CramersRuleOQ01OQ02OQ01`) to general n×n matrices.

## Definition (Route A — commutative, S2)

For an `(n+1)×(n+1)` matrix `A` over a field `F`, the (i,j)-quasideterminant
is the quotient
  `qdetF A i j  :=  det(A) / det(minor_{ij}(A))`,
where `minor_{ij}(A) := A.submatrix (Fin.succAbove i) (Fin.succAbove j)`
is the complementary n×n submatrix. This is uniform in n. The 3×3
specialization recovers `CramersRuleOQ01OQ02OQ01.qdet3` by `rfl`, and the
2×2 specializations recover `CramersRuleOQ01OQ02.qdet00` / `qdet11`
(modulo the standard non-degeneracy hypotheses).

## Definition (Route B — non-commutative, S3 SCAFFOLD)

Over a division ring `D`, the Gelfand–Retakh Schur recurrence asserts
  `qdetN A i j = A i j − ∑_{p,q : Fin n}  A i (succAbove j q) · Minv q p ·
                                            A (succAbove i p) j`
where `Minv` is the homological-relations inverse of the complementary
`n×n` minor `M := A.submatrix (succAbove i) (succAbove j)`.

The mutual recursion `qdetN` ↔ `qdetN_inv` is deferred to S4. S3 supplies
the **one-step Schur formula** `qdetN_step` (taking `Minv` as input),
which is non-recursive and reusable as the building block of either:
* a structural-recursion approach over `n` (matching `Σ n, Matrix _ _ D`), or
* an `Invertible (minorIJ A i j)`-parameterised formulation that avoids
  mutual recursion entirely by treating the inverse as a typeclass input.

Both routes converge on `qdetN_step A i j Minv`; only the construction of
`Minv` differs. The field-consistency theorem `qdetN_step_eq_qdetF` (S3,
sorry) anchors the recurrence: over a field, choosing `Minv := M⁻¹`
recovers `(-1)^(i+j) * qdetF A i j = det(A) / det(M)` up to the cofactor
sign factor (the unsigned form is false for off-diagonal pivots; see the
theorem docstring below).

## Main results

- `qdetF` (S2): uniform Route-A definition.
- `qdetF_field_quotient` (S2): defining multiplicative identity.
- `qdetF_ne_zero` (S2): nonvanishing.
- `qdetF_eq_qdet3` (S2): n=3 reduces to parent's `qdet3` by `rfl`.
- `qdetF_eq_qdet00` / `qdetF_eq_qdet11` (S2): n=2 specializations.
- `qdetN_step` (S3): non-recursive Schur formula over a division ring.
- `qdetN_step_zero_minv` (S3): degenerate case `Minv = 0` gives `A i j`.
- `qdetN_step_eq_qdetF_aux` (S4, sorry): division-free Schur–cofactor
  polynomial identity `det M · A i j − Σ adj(M) = (-1)^(i+j) · det A`; the
  sole remaining crux.
- `qdetN_step_eq_qdetF` (S4): field-consistency, signed-RHS form
  `(-1)^(i+j) * qdetF`, now PROVED as an algebraic consequence of the aux
  identity (clear the `det M` denominator). Previously a strategic sorry.

## References

- Gelfand, Retakh: "Determinants of matrices over noncommutative rings" (1991)
- Gelfand, Retakh, Serconek, Wilson: "Quasideterminants" (2005)
-/

noncomputable section

namespace CramersRuleOQ01OQ02OQ01OQ01

open Matrix

variable {F : Type*} [Field F]

-- ============================================================
-- PART I: The Complementary `(n)×(n)` Submatrix
-- ============================================================

/-- The complementary `n×n` submatrix of an `(n+1)×(n+1)` matrix: delete row
`i` and column `j`. Generalizes `CramersRuleOQ01OQ02OQ01.block3`. -/
abbrev minorIJ {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) F) (i j : Fin (n+1)) :
    Matrix (Fin n) (Fin n) F :=
  A.submatrix (Fin.succAbove i) (Fin.succAbove j)

-- ============================================================
-- PART II: The Uniform-in-n Quasideterminant
-- ============================================================

/-- **Definition (Route A — commutative).** The (i,j)-quasideterminant of an
`(n+1)×(n+1)` matrix `A` over a field, as the quotient
`det(A) / det(minor_{ij}(A))`. Generalizes the 2×2 `qdet00`-formula and the
3×3 `qdet3` uniformly in n.

Note: this is the canonical Gelfand–Retakh quasideterminant in its
*commutative* (Schur-complement-as-quotient) form. The fully non-commutative
inductive definition `qdetN` over a division ring is the S3 target. -/
def qdetF {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) F) (i j : Fin (n+1)) : F :=
  A.det / (minorIJ A i j).det

/-- **Core identity (Route A).** Multiplying by the minor determinant
recovers `det A`, provided the minor is invertible. This is the
multiplicative form of the defining identity and the n×n analogue of
`CramersRuleOQ01OQ02OQ01.qdet3_mul_minor_eq_det`. -/
theorem qdetF_field_quotient {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) F) (i j : Fin (n+1))
    (h : (minorIJ A i j).det ≠ 0) :
    qdetF A i j * (minorIJ A i j).det = A.det :=
  div_mul_cancel₀ _ h

/-- **Non-vanishing.** If both `det A` and the minor determinant are nonzero,
the quasideterminant is nonzero. Generalizes
`CramersRuleOQ01OQ02OQ01.qdet3_ne_zero`. -/
theorem qdetF_ne_zero {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) F) (i j : Fin (n+1))
    (hA : A.det ≠ 0) (hM : (minorIJ A i j).det ≠ 0) :
    qdetF A i j ≠ 0 :=
  div_ne_zero hA hM

-- ============================================================
-- PART III: n = 3 Specialization
-- ============================================================

/-- **n=3 specialization.** `qdetF` at `n+1 = 3` (i.e. `n = 2`) coincides
with the 3×3 quasideterminant `CramersRuleOQ01OQ02OQ01.qdet3`. Holds by
`rfl` because `block3` is defined exactly as
`A.submatrix (Fin.succAbove i) (Fin.succAbove j)` and is an `abbrev`. -/
theorem qdetF_eq_qdet3 (A : Matrix (Fin 3) (Fin 3) F) (i j : Fin 3) :
    qdetF A i j = CramersRuleOQ01OQ02OQ01.qdet3 A i j := rfl

-- ============================================================
-- PART IV: n = 2 Specialization (Schur form, via qdet00/qdet11)
-- ============================================================

/-- Determinant of the (0,0)-minor of a 2×2 matrix: this is the singleton
matrix `[[A 1 1]]`, whose determinant is `A 1 1`. -/
@[simp] lemma minorIJ_22_00_det (A : Matrix (Fin 2) (Fin 2) F) :
    (minorIJ A 0 0).det = A 1 1 := by
  -- The 1×1 minor has the single entry `A (succAbove 0 0) (succAbove 0 0)`
  -- = `A 1 1`. We pin this via `det_fin_one` + explicit evaluation.
  rw [show (minorIJ A 0 0).det = (minorIJ A 0 0) 0 0 from Matrix.det_fin_one _]
  show A (Fin.succAbove (0 : Fin 2) (0 : Fin 1))
        (Fin.succAbove (0 : Fin 2) (0 : Fin 1)) = A 1 1
  rfl

/-- Determinant of the (1,1)-minor of a 2×2 matrix: this is the singleton
matrix `[[A 0 0]]`, whose determinant is `A 0 0`. -/
@[simp] lemma minorIJ_22_11_det (A : Matrix (Fin 2) (Fin 2) F) :
    (minorIJ A 1 1).det = A 0 0 := by
  rw [show (minorIJ A 1 1).det = (minorIJ A 1 1) 0 0 from Matrix.det_fin_one _]
  show A (Fin.succAbove (1 : Fin 2) (0 : Fin 1))
        (Fin.succAbove (1 : Fin 2) (0 : Fin 1)) = A 0 0
  rfl

/-- **n=2 (0,0)-specialization.** Under `A 1 1 ≠ 0`, `qdetF A 0 0`
coincides with the 2×2 (0,0)-quasideterminant
`CramersRuleOQ01OQ02.qdet00 A`. The hypothesis is the same one carried in
the parent file's `qdet00_mul_eq_det`. -/
theorem qdetF_eq_qdet00 (A : Matrix (Fin 2) (Fin 2) F) (h : A 1 1 ≠ 0) :
    qdetF A 0 0 = CramersRuleOQ01OQ02.qdet00 A := by
  -- Strategy: show both sides multiply against `A 1 1` to give `A.det`,
  -- then cancel.
  have hMinor : (minorIJ A 0 0).det = A 1 1 := minorIJ_22_00_det A
  have hMinor_ne : (minorIJ A 0 0).det ≠ 0 := by rw [hMinor]; exact h
  have lhs_mul : qdetF A 0 0 * A 1 1 = A.det := by
    have := qdetF_field_quotient A 0 0 hMinor_ne
    rwa [hMinor] at this
  have rhs_mul : CramersRuleOQ01OQ02.qdet00 A * A 1 1 = A.det :=
    CramersRuleOQ01OQ02.qdet00_mul_eq_det A h
  exact mul_right_cancel₀ h (lhs_mul.trans rhs_mul.symm)

/-- **n=2 (1,1)-specialization.** Under `A 0 0 ≠ 0`, `qdetF A 1 1`
coincides with the 2×2 (1,1)-quasideterminant
`CramersRuleOQ01OQ02.qdet11 A`. -/
theorem qdetF_eq_qdet11 (A : Matrix (Fin 2) (Fin 2) F) (h : A 0 0 ≠ 0) :
    qdetF A 1 1 = CramersRuleOQ01OQ02.qdet11 A := by
  have hMinor : (minorIJ A 1 1).det = A 0 0 := minorIJ_22_11_det A
  have hMinor_ne : (minorIJ A 1 1).det ≠ 0 := by rw [hMinor]; exact h
  have lhs_mul : qdetF A 1 1 * A 0 0 = A.det := by
    have := qdetF_field_quotient A 1 1 hMinor_ne
    rwa [hMinor] at this
  -- Parent gives `A 0 0 * qdet11 A = A.det`; rewrite to `qdet11 A * A 0 0`.
  have rhs_mul : CramersRuleOQ01OQ02.qdet11 A * A 0 0 = A.det := by
    rw [mul_comm]; exact CramersRuleOQ01OQ02.mul_qdet11_eq_det A h
  exact mul_right_cancel₀ h (lhs_mul.trans rhs_mul.symm)

-- ============================================================
-- PART V: Summary
-- ============================================================

/-- **Route-A summary.** The uniform quasideterminant `qdetF` satisfies the
multiplicative defining identity at every n, generalizes both the
2×2 `qdet00`/`qdet11` and the 3×3 `qdet3` constructions in their
non-degenerate regimes, and provides the commutative foundation on which
the non-commutative `qdetN` (S3) will be built. -/
theorem qdetF_summary {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) F) (i j : Fin (n+1))
    (h : (minorIJ A i j).det ≠ 0) :
    qdetF A i j * (minorIJ A i j).det = A.det ∧
    qdetF A i j = A.det / (minorIJ A i j).det :=
  ⟨qdetF_field_quotient A i j h, rfl⟩

-- ============================================================
-- PART VI: Non-commutative Schur Step (S3 SCAFFOLD)
-- ============================================================

section NonCommutative

variable {D : Type*} [DivisionRing D]

/-- **Non-commutative one-step Schur formula (Route B, S3 SCAFFOLD).**

Given an `(n+1)×(n+1)` matrix `A` over a division ring `D`, indices
`i j : Fin (n+1)`, and an explicit `n×n` matrix `Minv` playing the role
of the (homological-relations) inverse of the complementary minor
`minorIJ A i j`, the Gelfand–Retakh Schur formula computes
  `A i j − ∑_{p,q : Fin n} A i (succAbove j q) · Minv q p ·
                            A (succAbove i p) j`.

This is the **one-step** form of the recurrence: it takes `Minv` as a
parameter and so is non-recursive. The full `qdetN` (S4) is obtained by
specialising `Minv := qdetN_inv (minorIJ A i j)` and folding the
mutual recursion. The advantage of separating `qdetN_step` is that:

* the field-consistency theorem `qdetN_step_eq_qdetF` (below, with sorry)
  proves the recurrence "for any inverse" once and for all — the choice
  of `Minv` is hidden behind a single hypothesis,
* the S4 mutual-recursion proof reduces to showing the constructed
  `qdetN_inv` satisfies the inverse-matrix equation, not to re-proving
  the entire recurrence at every level. -/
def qdetN_step {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) D)
    (i j : Fin (n+1)) (Minv : Matrix (Fin n) (Fin n) D) : D :=
  A i j -
    ∑ p : Fin n, ∑ q : Fin n,
      A i (Fin.succAbove j q) * Minv q p * A (Fin.succAbove i p) j

/-- **Degenerate inverse.** With `Minv = 0`, the Schur correction term
vanishes and `qdetN_step A i j 0 = A i j`. This is the trivial base
identity guaranteeing the formula is correctly anchored. -/
@[simp] theorem qdetN_step_zero_minv {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) D) (i j : Fin (n+1)) :
    qdetN_step A i j (0 : Matrix (Fin n) (Fin n) D) = A i j := by
  simp only [qdetN_step, Matrix.zero_apply, mul_zero, zero_mul,
    Finset.sum_const_zero, sub_zero]

/-- **Schur–cofactor polynomial identity (S4, division-free crux).**

The combinatorial heart of field consistency, stated over the commutative
ring `F` *without any division*. Writing `M := minorIJ A i j` for the
complementary minor, this is the polynomial identity

  `det M · A i j − ∑_{p,q} A i (succAbove j q) · adj(M) q p · A (succAbove i p) j
      = (-1)^(i+j) · det A`.

It is the Schur-complement / matrix-determinant identity in adjugate form:
multiplying the Route-B Schur step `A i j − bᵀ M⁻¹ c` through by `det M` and
using `M⁻¹ = (det M)⁻¹ • adj M` turns the field-valued statement into this
purely polynomial one. Verified by hand at `n = 0` (both sides `A 0 0`),
`n = 1` diagonal `(0,0)` (`A11·A00 − A01·A10 = det A`) and off-diagonal
`(0,1)` (`A10·A01 − A00·A11 = −det A`).

The main field-consistency theorem `qdetN_step_eq_qdetF` is a one-line
algebraic consequence (clear the `det M` denominator). This lemma isolates
the only genuinely non-trivial content: the cofactor/Schur identity. -/
theorem qdetN_step_eq_qdetF_aux {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) F) (i j : Fin (n+1)) :
    (minorIJ A i j).det * A i j
      - ∑ p : Fin n, ∑ q : Fin n,
          A i (Fin.succAbove j q) * (minorIJ A i j).adjugate q p
            * A (Fin.succAbove i p) j
      = (-1 : F) ^ ((i : ℕ) + (j : ℕ)) * A.det := by
  sorry

/-- **Field consistency (S4, PROVED modulo the polynomial crux).**

Now derived from `qdetN_step_eq_qdetF_aux` by a short field-algebra step:
expand `(minorIJ A i j)⁻¹ = (det M)⁻¹ • adj M`, factor the scalar out of the
Schur double sum, substitute the division-free identity, and clear the
`det M` denominator. The only remaining `sorry` in this file is the
division-free polynomial crux `aux`, not this theorem.

Over a field `F`, choosing `Minv := (minorIJ A i j)⁻¹` (Mathlib's
`Matrix.nonsingInv`) inside `qdetN_step` recovers the Route-A quotient
`qdetF A i j = det A / det(minor)` up to the cofactor sign
`(-1)^(i+j)`. This is the bridge between the commutative (S2) and
non-commutative (S3-Route-B) formulations.

**Why the `(-1)^(i+j)` factor.** Verified by S4c PREP §2 against
`A = ⟦1 2; 3 4⟧` at all four `(i,j) ∈ Fin 2 × Fin 2` pivots:
the ratio `qdetN_step / qdetF` is `+1` at the diagonal `(0,0)` and
`(1,1)` but `-1` at the off-diagonal `(0,1)` and `(1,0)`, matching
`(-1)^(i+j)` exactly. The S4 PREP block-Schur reshape derives this
algebraically from `sign(Fin.cycleRange i .symm) * sign(Fin.cycleRange j) = (-1)^i * (-1)^j`.
The earlier S3 SCAFFOLD statement (without the sign factor) was
mathematically false for off-diagonal pivots; this correction has zero
impact on `qdetN_step_zero_minv` (the `Minv = 0` base case is unsigned
because the field-consistency theorem only fires when `M⁻¹ = (minorIJ).⁻¹`).

**Proof strategy (S4).** Expand `Matrix.inv_def`:
  `(minorIJ A i j)⁻¹ = (1 / (minorIJ A i j).det) • (minorIJ A i j).adjugate`,
factor out the scalar `1 / det(minor)`, and apply
`Matrix.det_eq_sum_mul_adjugate_row` (per S4e PREP §2 — cleaner than
`Matrix.det_succ_row` because cofactor signs are baked into adjugate
notation). Splitting the row-`i` sum at column `k = j` isolates
`A i j * adjugate A j i + ∑_{k≠j} A i k * adjugate A k i = A.det`;
unfolding the adjugate entries via
`Matrix.adjugate_fin_succ_eq_det_submatrix` and re-indexing the
`k ≠ j` sum via `Fin.sum_univ_succAbove` collects the `(-1)^(i+j)`
factor on the `A.det / minor.det` quotient, yielding the signed
field-consistency identity.

Estimated S4 proof size: ~55–85 Lean lines (the cofactor-sum
re-indexing through `Fin.succAbove`'s sign convention is the main
mechanical step). See S4e PREP §3 for the LOC table. -/
theorem qdetN_step_eq_qdetF {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) F) (i j : Fin (n+1))
    (h : (minorIJ A i j).det ≠ 0) :
    qdetN_step A i j (minorIJ A i j)⁻¹
      = (-1 : F) ^ ((i : ℕ) + (j : ℕ)) * qdetF A i j := by
  have haux := qdetN_step_eq_qdetF_aux A i j
  -- Entrywise inverse: `(minorIJ A i j)⁻¹ q p = (det M)⁻¹ * adj M q p`.
  have hsmul : ∀ q p : Fin n, ((minorIJ A i j)⁻¹) q p
      = ((minorIJ A i j).det)⁻¹ * (minorIJ A i j).adjugate q p := by
    intro q p
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul]
  -- Factor the scalar `(det M)⁻¹` out of the Schur double sum.
  have hsum : (∑ p : Fin n, ∑ q : Fin n,
        A i (Fin.succAbove j q) * ((minorIJ A i j)⁻¹) q p * A (Fin.succAbove i p) j)
      = ((minorIJ A i j).det)⁻¹ * ∑ p : Fin n, ∑ q : Fin n,
        A i (Fin.succAbove j q) * (minorIJ A i j).adjugate q p
          * A (Fin.succAbove i p) j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hsmul q p]; ring
  simp only [qdetN_step, qdetF]
  rw [hsum]
  -- Replace the (signed) adjugate sum `S` via the polynomial crux `haux`.
  have hSval : (∑ p : Fin n, ∑ q : Fin n,
        A i (Fin.succAbove j q) * (minorIJ A i j).adjugate q p
          * A (Fin.succAbove i p) j)
      = (minorIJ A i j).det * A i j - (-1 : F) ^ ((i : ℕ) + (j : ℕ)) * A.det := by
    linear_combination -haux
  rw [hSval]
  field_simp
  ring

/-- **Field consistency at n = 0 (1×1 matrices), base case.** Concrete-witness
specialisation of `qdetN_step_eq_qdetF` to 1×1 matrices, proved without
invoking the strategic sorry. The double sum defining `qdetN_step` is
indexed by `Fin 0 × Fin 0` (empty), and the complementary `minorIJ` is
the empty 0×0 matrix with determinant 1. Both sides collapse to `A 0 0`
and the cofactor sign `(-1)^(0+0) = 1` is trivial. This grounds the
strategic theorem's signed RHS at the smallest case (the n=2 and n=3
specialisations already proved in Parts III–IV use the parent files'
`qdet00`/`qdet11`/`qdet3` definitions instead of `qdetN_step`, so this
is the first verification connecting `qdetN_step` directly to `qdetF`). -/
theorem qdetN_step_eq_qdetF_fin_one
    (A : Matrix (Fin 1) (Fin 1) F) (i j : Fin 1)
    (_h : (minorIJ A i j).det ≠ 0) :
    qdetN_step A i j (minorIJ A i j)⁻¹
      = (-1 : F) ^ ((i : ℕ) + (j : ℕ)) * qdetF A i j := by
  fin_cases i
  fin_cases j
  simp [qdetN_step, qdetF]

end NonCommutative

end CramersRuleOQ01OQ02OQ01OQ01

end
