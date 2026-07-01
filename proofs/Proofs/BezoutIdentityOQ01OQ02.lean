import Mathlib

/-
# Bézout's Identity via Unimodular 2×2 Integer Matrices

## Open Question (bezout-identity-oq-01-oq-02)
Connect the extended Euclidean algorithm (`extGcd`, from `bezout-identity-oq-01`)
to matrix arithmetic: the algorithm corresponds to unimodular 2×2 integer matrices.

## What This Proves
The extended Euclidean algorithm is the story of `SL₂(ℤ)` acting on integer columns:

1. **Elementary step is unimodular.** Each division step of the algorithm is
   left-multiplication by the elementary matrix `eStep q = !![0, 1; 1, -q]`, which
   has determinant `-1` (`eStep_det`) and realises one round of Euclid,
   `(a, b) ↦ (b, a % b)` (`eStep_euclid`).

2. **Unimodularity is preserved.** Since `det` is multiplicative, matrices of
   determinant `±1` are closed under multiplication (`det_mul_unimodular`); hence the
   composite of the elementary steps is again unimodular.

3. **The Bézout matrix lands in `SL₂(ℤ)`.** The accumulated transform is the Bézout
   coefficient matrix `bezoutMatrix a b = !![x, y; -b/g, a/g]` where `g = gcd a b`
   and `g = a·x + b·y`. It has determinant `1` (`bezoutMatrix_det`) and carries the
   column `(a, b)ᵀ` to `(g, 0)ᵀ` (`bezoutMatrix_mulVec`).

4. **Main theorem** (`bezout_unimodular_reduction`): for `(a, b) ≠ (0, 0)` there is a
   matrix in `SL₂(ℤ)` reducing `(a, b)ᵀ` to `(gcd a b, 0)ᵀ`. This is the matrix form
   of Bézout's identity.

## Approach
Purely algebraic. The Bézout coefficients come from Mathlib's `Int.gcd_eq_gcd_ab`; the
determinant and action identities are settled by clearing the exact integer divisions
`g ∣ a`, `g ∣ b` and one `linear_combination` against Bézout's identity.
-/

namespace BezoutIdentityOQ01OQ02

open Matrix

/-! ## Elementary Euclidean-step matrices -/

/-- Elementary Euclidean-step matrix for quotient `q`: it swaps the two entries and
subtracts `q` times the new second entry from the first. One division step of the
extended Euclidean algorithm is left-multiplication by this matrix. -/
def eStep (q : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, -q]

/-- Every elementary step matrix is unimodular: its determinant is `-1`. -/
@[simp] theorem eStep_det (q : ℤ) : (eStep q).det = -1 := by
  simp [eStep, Matrix.det_fin_two_of]

/-- Action of an elementary step on a column: `(a, b) ↦ (b, a - q·b)`. -/
theorem eStep_apply (q a b : ℤ) : eStep q *ᵥ ![a, b] = ![b, a - q * b] := by
  funext i
  fin_cases i <;>
    simp [eStep, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- With the true quotient `q = a / b`, one elementary step realises one round of the
Euclidean algorithm: `(a, b) ↦ (b, a % b)`. -/
theorem eStep_euclid (a b : ℤ) : eStep (a / b) *ᵥ ![a, b] = ![b, a % b] := by
  rw [eStep_apply]
  have h : a - a / b * b = a % b := by rw [Int.emod_def]; ring
  rw [h]

/-- Determinant is multiplicative, so unimodular matrices (det `±1`) are closed under
multiplication: the composite of Euclidean steps stays unimodular. -/
theorem det_mul_unimodular {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℤ)
    (hM : M.det = 1 ∨ M.det = -1) (hN : N.det = 1 ∨ N.det = -1) :
    (M * N).det = 1 ∨ (M * N).det = -1 := by
  rw [Matrix.det_mul]
  rcases hM with h | h <;> rcases hN with h' | h' <;> rw [h, h'] <;> omega

/-- Action of a general `2×2` matrix on a two-element column. -/
theorem mulVec_two (p q r s a b : ℤ) :
    !![p, q; r, s] *ᵥ ![a, b] = ![p * a + q * b, r * a + s * b] := by
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-! ## The Bézout coefficient matrix -/

/-- The Bézout coefficient matrix for `a, b`. Its first row holds the Bézout
coefficients `(gcdA, gcdB)` (with `a·gcdA + b·gcdB = gcd a b`); its second row holds
`(-b/g, a/g)`, so that the matrix reduces `(a, b)ᵀ` to `(g, 0)ᵀ`. -/
def bezoutMatrix (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![Int.gcdA a b, Int.gcdB a b;
     -(b / (Int.gcd a b : ℤ)), a / (Int.gcd a b : ℤ)]

/-- The gcd is nonzero whenever the inputs are not both zero. -/
theorem gcd_cast_ne_zero (a b : ℤ) (h : a ≠ 0 ∨ b ≠ 0) : (Int.gcd a b : ℤ) ≠ 0 := by
  rw [Ne, Int.natCast_eq_zero, Int.gcd_eq_zero_iff]
  tauto

/-- **The Bézout matrix lies in `SL₂(ℤ)`.** Its determinant is `1`. -/
theorem bezoutMatrix_det (a b : ℤ) (h : a ≠ 0 ∨ b ≠ 0) :
    (bezoutMatrix a b).det = 1 := by
  have hg : (Int.gcd a b : ℤ) ≠ 0 := gcd_cast_ne_zero a b h
  have hda : a / (Int.gcd a b : ℤ) * (Int.gcd a b : ℤ) = a :=
    Int.ediv_mul_cancel (Int.gcd_dvd_left ..)
  have hdb : b / (Int.gcd a b : ℤ) * (Int.gcd a b : ℤ) = b :=
    Int.ediv_mul_cancel (Int.gcd_dvd_right ..)
  have hbez : a * Int.gcdA a b + b * Int.gcdB a b = (Int.gcd a b : ℤ) :=
    (Int.gcd_eq_gcd_ab a b).symm
  have key : (Int.gcd a b : ℤ) * (bezoutMatrix a b).det = (Int.gcd a b : ℤ) := by
    rw [bezoutMatrix, Matrix.det_fin_two_of]
    have expand :
        (Int.gcd a b : ℤ) *
            (Int.gcdA a b * (a / (Int.gcd a b : ℤ)) -
              Int.gcdB a b * -(b / (Int.gcd a b : ℤ)))
          = Int.gcdA a b * (a / (Int.gcd a b : ℤ) * (Int.gcd a b : ℤ)) +
              Int.gcdB a b * (b / (Int.gcd a b : ℤ) * (Int.gcd a b : ℤ)) := by ring
    rw [expand, hda, hdb]
    linear_combination hbez
  have key' : (Int.gcd a b : ℤ) * (bezoutMatrix a b).det = (Int.gcd a b : ℤ) * 1 := by
    rw [key, mul_one]
  exact mul_left_cancel₀ hg key'

/-- **The Bézout matrix reduces `(a, b)ᵀ` to `(gcd a b, 0)ᵀ`.** -/
theorem bezoutMatrix_mulVec (a b : ℤ) (h : a ≠ 0 ∨ b ≠ 0) :
    bezoutMatrix a b *ᵥ ![a, b] = ![(Int.gcd a b : ℤ), 0] := by
  have hg : (Int.gcd a b : ℤ) ≠ 0 := gcd_cast_ne_zero a b h
  have hda : a / (Int.gcd a b : ℤ) * (Int.gcd a b : ℤ) = a :=
    Int.ediv_mul_cancel (Int.gcd_dvd_left ..)
  have hdb : b / (Int.gcd a b : ℤ) * (Int.gcd a b : ℤ) = b :=
    Int.ediv_mul_cancel (Int.gcd_dvd_right ..)
  have hbez : a * Int.gcdA a b + b * Int.gcdB a b = (Int.gcd a b : ℤ) :=
    (Int.gcd_eq_gcd_ab a b).symm
  -- Entry 0 : gcdA · a + gcdB · b = gcd a b (Bézout's identity)
  have e0 : Int.gcdA a b * a + Int.gcdB a b * b = (Int.gcd a b : ℤ) := by
    linear_combination hbez
  -- Entry 1 : (-b/g) · a + (a/g) · b = 0 (clear the exact divisions, then cancel g)
  have e1 : -(b / (Int.gcd a b : ℤ)) * a + a / (Int.gcd a b : ℤ) * b = 0 := by
    have key :
        (Int.gcd a b : ℤ) *
            (-(b / (Int.gcd a b : ℤ)) * a + a / (Int.gcd a b : ℤ) * b)
          = (Int.gcd a b : ℤ) * 0 := by
      have e :
          (Int.gcd a b : ℤ) *
              (-(b / (Int.gcd a b : ℤ)) * a + a / (Int.gcd a b : ℤ) * b)
            = -(b / (Int.gcd a b : ℤ) * (Int.gcd a b : ℤ)) * a +
                a / (Int.gcd a b : ℤ) * (Int.gcd a b : ℤ) * b := by ring
      rw [e, hda, hdb]; ring
    exact mul_left_cancel₀ hg key
  rw [bezoutMatrix, mulVec_two, e0, e1]

/-! ## Membership in the special linear group -/

/-- The Bézout matrix packaged as an element of the special linear group `SL₂(ℤ)`. -/
def bezoutSL (a b : ℤ) (h : a ≠ 0 ∨ b ≠ 0) : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨bezoutMatrix a b, bezoutMatrix_det a b h⟩

/-- **Main theorem — matrix form of Bézout's identity.** For `(a, b) ≠ (0, 0)` there is
a matrix in `SL₂(ℤ)` (the Bézout matrix) carrying `(a, b)ᵀ` to `(gcd a b, 0)ᵀ`. This is
the extended Euclidean algorithm read off as a single unimodular transformation. -/
theorem bezout_unimodular_reduction (a b : ℤ) (h : a ≠ 0 ∨ b ≠ 0) :
    ∃ M : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      (M : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![a, b] = ![(Int.gcd a b : ℤ), 0] := by
  refine ⟨bezoutSL a b h, ?_⟩
  simpa [bezoutSL] using bezoutMatrix_mulVec a b h

/-! ## Worked examples -/

/-- One concrete Euclidean step via its elementary matrix: `(17, 5) ↦ (5, 17 % 5)`. -/
example : eStep (17 / 5) *ᵥ ![17, 5] = ![5, 17 % 5] := eStep_euclid 17 5

/-- A concrete unimodular reduction: some `SL₂(ℤ)` matrix sends `(12, 18)ᵀ` to
`(6, 0)ᵀ`, and indeed `gcd 12 18 = 6`. -/
example : ∃ M : Matrix.SpecialLinearGroup (Fin 2) ℤ,
    (M : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![12, 18] = ![(6 : ℤ), 0] := by
  refine ⟨bezoutSL 12 18 (by norm_num), ?_⟩
  have h := bezoutMatrix_mulVec 12 18 (by norm_num)
  have hgcd : (Int.gcd 12 18 : ℤ) = 6 := by decide
  rw [hgcd] at h
  simpa [bezoutSL] using h

end BezoutIdentityOQ01OQ02
