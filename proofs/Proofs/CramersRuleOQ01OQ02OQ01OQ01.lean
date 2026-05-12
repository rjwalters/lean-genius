import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import Proofs.CramersRuleOQ01OQ02
import Proofs.CramersRuleOQ01OQ02OQ01

/-
# Inductive n×n Quasideterminant Theory over a Field
# (cramers-rule-oq-01-oq-02-oq-01-oq-01) — S2

This is the **commutative half** (Route A) of the open question stated in
`CramersRuleOQ01OQ02OQ01.lean` lines 29–36: extend the 2×2 / 3×3
Gelfand–Retakh quasideterminant theory to general n×n matrices.

The fully non-commutative theory over division rings (Route B —
`qdetN` via mutual strong recursion with `qdetN_inv`) is deferred to S3.

## Definition (Route A — commutative)

For an `(n+1)×(n+1)` matrix `A` over a field `F`, the (i,j)-quasideterminant
is the quotient
  `qdetF A i j  :=  det(A) / det(minor_{ij}(A))`,
where `minor_{ij}(A) := A.submatrix (Fin.succAbove i) (Fin.succAbove j)`
is the complementary n×n submatrix.

This is uniform in n. The 3×3 specialization recovers
`CramersRuleOQ01OQ02OQ01.qdet3` by `rfl`, and the 2×2 (0,0)-specialization
recovers `CramersRuleOQ01OQ02.qdet00` (modulo the standard `A 1 1 ≠ 0`
non-degeneracy hypothesis carried in the parent's
`qdet00_mul_eq_det`).

## Main results

- `qdetF`: uniform definition.
- `qdetF_field_quotient`: the defining multiplicative identity
  `qdetF A i j * det(minor) = det(A)` (provided `det(minor) ≠ 0`).
- `qdetF_ne_zero`: nonvanishing.
- `qdetF_eq_qdet3`: n=3 reduces to `CramersRuleOQ01OQ02OQ01.qdet3` (`rfl`).
- `qdetF_eq_qdet00`: n=2 (0,0)-case reduces to
  `CramersRuleOQ01OQ02.qdet00` (under `A 1 1 ≠ 0`).
- `qdetF_eq_qdet11`: n=2 (1,1)-case reduces to
  `CramersRuleOQ01OQ02.qdet11` (under `A 0 0 ≠ 0`).

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

end CramersRuleOQ01OQ02OQ01OQ01

end
