/-
  The orthogonal analogue of `det : U(n) → U(1)`:  `det O = ±1` for `OᵀO = 1`.

  The parent entry (`det Mᴴ = star (det M)`) derives, over `ℂ`, that a unitary
  matrix `U` (`Uᴴ U = 1`) has `‖det U‖ = 1` — the determinant map `U(n) → U(1)`.
  Its open question #3 asks for the *real orthogonal* analogue: what is `det O`
  when `Oᵀ O = 1`?

  Replacing the conjugate transpose `ᴴ` by the plain transpose `ᵀ` collapses the
  scalar relation.  Applying `det` to `Oᵀ O = 1` and using `det Oᵀ = det O`
  (rather than `det Uᴴ = star (det U)`) gives

      (det O)² = 1,

  so over any integral domain `det O = 1` or `det O = -1`, and over `ℝ`
  `|det O| = 1`.  Where the unitary determinant ranges over the whole unit
  *circle* `U(1)`, the orthogonal determinant is pinned to the two-element group
  `{±1}`.  This is the determinant **sign character** `O(n) → {±1}`, whose kernel
  is exactly the special orthogonal group `SO(n)`.

  Contents:
    * `det_mul_self_of_orthogonal` — the ring-level identity `(det O)² = 1`
      (holds over any `CommRing`; this is the shared core).
    * `isUnit_det_of_orthogonal`   — hence `det O` is a unit.
    * `det_eq_one_or_neg_one_of_orthogonal` — over an integral domain, `det O = ±1`.
    * `real_orthogonal_det`, `abs_det_eq_one_of_orthogonal` — the `ℝ` headline.
    * `orthogonal_mul` — the orthogonal matrices are closed under products, so the
      sign is multiplicative: `O(n) → {±1}` is a group homomorphism.
    * `mem_orthogonalGroup_of_transpose_mul`, `mem_specialOrthogonalGroup_iff_det_one`
      — `SO(n)` is exactly the `det = 1` fibre (the kernel of the sign character).
    * Worked instances: the identity has sign `+1`; the reflection `diag(-1, 1)`
      is orthogonal with sign `-1`, so the character hits both values.

  Verified: 0 sorries, 0 axioms (only propext / Classical.choice / Quot.sound;
  no native_decide, no Lean.ofReduceBool).
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Matrix

-- Mathlib's `Matrix.orthogonalGroup` / `specialOrthogonalGroup` are the unitary
-- groups taken with the trivial `star = id` ring structure on a commutative ring,
-- so working with them requires that star structure in scope.
attribute [local instance] starRingOfComm

namespace DetConjugateTransposeOQ01OQ03

/-! ### The shared core: `(det O)² = 1` over any commutative ring -/

/-- **Orthogonal determinant squares to one.**  If `Oᵀ * O = 1` then
`det O * det O = 1`.  This is the transpose analogue of
`star (det U) * det U = 1` for the unitary case: applying `det` to `Oᵀ O = 1`
and using `det Oᵀ = det O` (in place of `det Uᴴ = star (det U)`) removes the
`star`, leaving a genuine square.  Holds over any `CommRing`. -/
theorem det_mul_self_of_orthogonal {R : Type*} [CommRing R]
    {n : Type*} [Fintype n] [DecidableEq n] {O : Matrix n n R}
    (hO : Oᵀ * O = 1) : det O * det O = 1 := by
  have h := congrArg det hO
  rwa [det_mul, det_transpose, det_one] at h

/-- The determinant of an orthogonal matrix is a unit (it is its own inverse). -/
theorem isUnit_det_of_orthogonal {R : Type*} [CommRing R]
    {n : Type*} [Fintype n] [DecidableEq n] {O : Matrix n n R}
    (hO : Oᵀ * O = 1) : IsUnit (det O) :=
  IsUnit.of_mul_eq_one _ (det_mul_self_of_orthogonal hO)

/-! ### Over an integral domain: `det O = ±1` -/

/-- **Orthogonal determinant is `±1`.**  Over any integral domain, `Oᵀ O = 1`
forces `det O = 1 ∨ det O = -1`.  Factor `(det O)² - 1 = (det O - 1)(det O + 1)`;
no zero divisors makes one factor vanish. -/
theorem det_eq_one_or_neg_one_of_orthogonal {R : Type*} [CommRing R] [IsDomain R]
    {n : Type*} [Fintype n] [DecidableEq n] {O : Matrix n n R}
    (hO : Oᵀ * O = 1) : det O = 1 ∨ det O = -1 := by
  have h : det O * det O = 1 := det_mul_self_of_orthogonal hO
  have hfac : (det O - 1) * (det O + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h1 | h1
  · exact Or.inl (sub_eq_zero.mp h1)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h1)

/-! ### The `ℝ` headline -/

/-- **Real orthogonal determinant is `±1`** (open question #3, verbatim).
For a real matrix with `Oᵀ O = 1`, `det O = 1 ∨ det O = -1`. -/
theorem real_orthogonal_det {n : Type*} [Fintype n] [DecidableEq n]
    {O : Matrix n n ℝ} (hO : Oᵀ * O = 1) : det O = 1 ∨ det O = -1 :=
  det_eq_one_or_neg_one_of_orthogonal hO

/-- **Real orthogonal determinant has absolute value one**: `|det O| = 1`.
The real shadow of the unitary `‖det U‖ = 1` — but confined to `{±1}` rather
than the whole unit circle. -/
theorem abs_det_eq_one_of_orthogonal {n : Type*} [Fintype n] [DecidableEq n]
    {O : Matrix n n ℝ} (hO : Oᵀ * O = 1) : |det O| = 1 := by
  rcases real_orthogonal_det hO with h | h <;> rw [h] <;> norm_num

/-! ### Multiplicativity: the sign character `O(n) → {±1}` -/

/-- **Orthogonal matrices are closed under multiplication**: if `Oᵀ O = 1` and
`Pᵀ P = 1` then `(O P)ᵀ (O P) = 1`.  Together with `det (O P) = det O · det P`
this makes the sign `det : O(n) → {±1}` a group homomorphism. -/
theorem orthogonal_mul {R : Type*} [CommRing R]
    {n : Type*} [Fintype n] [DecidableEq n] {O P : Matrix n n R}
    (hO : Oᵀ * O = 1) (hP : Pᵀ * P = 1) : (O * P)ᵀ * (O * P) = 1 := by
  rw [transpose_mul, mul_assoc, ← mul_assoc Oᵀ O P, hO, one_mul, hP]

/-- The sign is multiplicative on orthogonal matrices: `det (O P) = det O · det P`,
each factor being `±1`.  (This is just `det_mul`, recorded here to make the
homomorphism `O(n) → {±1}` explicit.) -/
theorem det_mul_of_orthogonal {R : Type*} [CommRing R]
    {n : Type*} [Fintype n] [DecidableEq n] (O P : Matrix n n R) :
    det (O * P) = det O * det P :=
  det_mul O P

/-! ### `SO(n)` is the kernel of the sign character -/

/-- Bridge to Mathlib's `orthogonalGroup`: `Oᵀ O = 1` means `O ∈ O(n)`. -/
theorem mem_orthogonalGroup_of_transpose_mul {R : Type*} [CommRing R]
    {n : Type*} [Fintype n] [DecidableEq n] {O : Matrix n n R}
    (hO : Oᵀ * O = 1) : O ∈ Matrix.orthogonalGroup n R :=
  (Matrix.mem_orthogonalGroup_iff' n R).mpr hO

/-- **`SO(n)` is the `det = 1` fibre.**  An orthogonal matrix lies in the special
orthogonal group iff its determinant is `1` — i.e. `SO(n)` is exactly the kernel
of the sign character `O(n) → {±1}`. -/
theorem mem_specialOrthogonalGroup_iff_det_one {R : Type*} [CommRing R]
    {n : Type*} [Fintype n] [DecidableEq n] {O : Matrix n n R}
    (hO : Oᵀ * O = 1) : O ∈ Matrix.specialOrthogonalGroup n R ↔ det O = 1 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  exact and_iff_right (mem_orthogonalGroup_of_transpose_mul hO)

/-! ### Worked instances: both signs are attained -/

/-- The identity is orthogonal with sign `+1`: it lies in `SO(n)`. -/
example : det (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := det_one

example : (1 : Matrix (Fin 2) (Fin 2) ℝ) ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ :=
  (mem_specialOrthogonalGroup_iff_det_one (by simp)).mpr det_one

/-- The reflection `diag(-1, 1)` is orthogonal (`Oᵀ O = 1`)… -/
theorem reflection_orthogonal :
    (!![(-1 : ℝ), 0; 0, 1])ᵀ * !![(-1 : ℝ), 0; 0, 1] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- …with sign `-1`.  So the sign character is onto `{±1}`, and this reflection
lies in `O(2) \ SO(2)`. -/
theorem reflection_det : det (!![(-1 : ℝ), 0; 0, 1]) = -1 := by
  rw [Matrix.det_fin_two_of]; ring

example : det (!![(-1 : ℝ), 0; 0, 1]) = 1 ∨ det (!![(-1 : ℝ), 0; 0, 1]) = -1 :=
  real_orthogonal_det reflection_orthogonal

/-- The reflection is *not* in `SO(2)`, confirming `SO(2) ⊊ O(2)`. -/
example : (!![(-1 : ℝ), 0; 0, 1]) ∉ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  rw [mem_specialOrthogonalGroup_iff_det_one reflection_orthogonal, reflection_det]
  norm_num

end DetConjugateTransposeOQ01OQ03
