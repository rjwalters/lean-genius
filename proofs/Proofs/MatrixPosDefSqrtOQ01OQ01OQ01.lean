/-
# The Operator Absolute Value `|A| = √(AᴴA)` and Norm Preservation

Follow-up to `matrix-posdef-sqrt-oq-01-oq-01`
(*Polar Decomposition `A = U·√(AᴴA)` from the Positive Semidefinite Square Root*).

The positive semidefinite factor `√(AᴴA)` appearing in the polar decomposition
`A = U · √(AᴴA)` is the **operator absolute value** (or *modulus*) `|A|`.  The
single most important structural fact about the modulus is that it acts on
lengths exactly as `A` does:

    ‖A x‖ = ‖ |A| x ‖      for every vector `x`.

Squaring, this is the identity of Hermitian quadratic forms

    ⟨Ax, Ax⟩ = ⟨x, AᴴA x⟩ = ⟨x, |A|² x⟩ = ⟨|A|x, |A|x⟩,

which uses only `|A|² = AᴴA` and the self-adjointness of `|A|`.  This is
precisely *why* the polar decomposition `A = U|A|` can be realised with a
genuinely **unitary** `U`: on the range of `|A|`, `A` and `|A|` have the same
length, so the transition map `U` is an isometry.

We work over an arbitrary `RCLike` field `𝕜` (so `ℝ` or `ℂ`) and prove:

* the purely algebraic quadratic-form identity
  `⟨Ax, Ax⟩ = ⟨|A|x, |A|x⟩` (`absValue_star_mulVec_dotProduct`), and
* the honest squared-Euclidean-norm identity
  `∑ᵢ ‖(Ax)ᵢ‖² = ∑ᵢ ‖(|A|x)ᵢ‖²` (`absValue_normSq_eq`).

The modulus is defined via Mathlib's continuous functional calculus
(`CFC.sqrt`), exactly as the polar factor of the parent entry.

Self-contained: imports Mathlib only.  No axioms beyond Mathlib.
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

open Matrix
open scoped MatrixOrder ComplexOrder

namespace MatrixPosDefSqrtOQ01OQ01OQ01

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The operator absolute value `|A| = √(AᴴA)` -/

/-- The **operator absolute value** (modulus) of a matrix `A`, defined as the
positive semidefinite square root of `Aᴴ · A`.  This is exactly the positive
semidefinite factor of the polar decomposition `A = U · |A|`. -/
noncomputable def absValue (A : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  CFC.sqrt (Aᴴ * A)

/-- `|A|` is positive semidefinite. -/
theorem absValue_posSemidef (A : Matrix n n 𝕜) : (absValue A).PosSemidef :=
  (CFC.sqrt_nonneg (Aᴴ * A)).posSemidef

/-- `|A|` is Hermitian. -/
theorem absValue_isHermitian (A : Matrix n n 𝕜) : (absValue A)ᴴ = absValue A :=
  (absValue_posSemidef A).isHermitian

/-- Defining property of the modulus: `|A|² = AᴴA`. -/
theorem absValue_mul_self (A : Matrix n n 𝕜) :
    absValue A * absValue A = Aᴴ * A :=
  CFC.sqrt_mul_sqrt_self (Aᴴ * A) (posSemidef_conjTranspose_mul_self A).nonneg

/-- `|A|ᴴ · |A| = AᴴA`.  Since `|A|` is Hermitian this is just the defining
property, but it is the form in which the modulus enters the quadratic form. -/
theorem absValue_conjTranspose_mul_self (A : Matrix n n 𝕜) :
    (absValue A)ᴴ * absValue A = Aᴴ * A := by
  rw [absValue_isHermitian, absValue_mul_self]

/-- **Characterisation of the modulus.** `|A|` is the unique positive
semidefinite matrix `P` with `P² = AᴴA`. -/
theorem absValue_unique (A P : Matrix n n 𝕜) (hP : P.PosSemidef)
    (h : P * P = Aᴴ * A) : P = absValue A :=
  (CFC.sqrt_unique h hP.nonneg).symm

/-! ### The fundamental quadratic-form identity -/

/-- For any matrix `M` and vector `x`, the (unconjugated) Hermitian quadratic
form of `M x` collapses to the form of `MᴴM` on `x`:
`⟨Mx, Mx⟩ = ⟨x, (MᴴM) x⟩`.  Purely algebraic — no analysis. -/
theorem star_mulVec_dotProduct_self (M : Matrix n n 𝕜) (x : n → 𝕜) :
    star (M *ᵥ x) ⬝ᵥ (M *ᵥ x) = star x ⬝ᵥ ((Mᴴ * M) *ᵥ x) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

/-- **Norm preservation (quadratic-form version).**  `A` and its modulus `|A|`
induce the *same* Hermitian quadratic form:
`⟨Ax, Ax⟩ = ⟨|A|x, |A|x⟩`.  This is the algebraic heart of why the unitary
factor of the polar decomposition is an isometry. -/
theorem absValue_star_mulVec_dotProduct (A : Matrix n n 𝕜) (x : n → 𝕜) :
    star (A *ᵥ x) ⬝ᵥ (A *ᵥ x)
      = star (absValue A *ᵥ x) ⬝ᵥ (absValue A *ᵥ x) := by
  rw [star_mulVec_dotProduct_self A x, star_mulVec_dotProduct_self (absValue A) x,
    absValue_conjTranspose_mul_self]

/-! ### The honest squared-norm identity -/

/-- The unconjugated form `star y ⬝ᵥ y` is the (real) squared Euclidean length
`∑ᵢ ‖yᵢ‖²`, transported into `𝕜`. -/
theorem dotProduct_star_self (y : n → 𝕜) :
    star y ⬝ᵥ y = ((∑ i, ‖y i‖ ^ 2 : ℝ) : 𝕜) := by
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, RCLike.conj_mul,
    RCLike.ofReal_sum, RCLike.ofReal_pow]

/-- **Norm preservation (Euclidean-norm version).**  `A` and its modulus `|A|`
send every vector to vectors of equal Euclidean length:
`∑ᵢ ‖(Ax)ᵢ‖² = ∑ᵢ ‖(|A|x)ᵢ‖²`, i.e. `‖Ax‖ = ‖|A|x‖`. -/
theorem absValue_normSq_eq (A : Matrix n n 𝕜) (x : n → 𝕜) :
    (∑ i, ‖(A *ᵥ x) i‖ ^ 2) = ∑ i, ‖(absValue A *ᵥ x) i‖ ^ 2 := by
  have h := absValue_star_mulVec_dotProduct A x
  rw [dotProduct_star_self, dotProduct_star_self] at h
  exact_mod_cast h

end MatrixPosDefSqrtOQ01OQ01OQ01
