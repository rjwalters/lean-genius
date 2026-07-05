import Mathlib.Analysis.Normed.Algebra.GelfandMazur
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Hurwitz Only-If: Normed Division Algebras Have Dimension in {1, 2, 4, 8}

This file addresses the "only-if" direction of Hurwitz's theorem (1898):
> If A is a finite-dimensional normed division algebra over ℝ, then dim(A) ∈ {1, 2, 4, 8}.

## Strategy

**Commutative case** (A is a field): Proved via the Gelfand-Mazur theorem (Mathlib, 2025).
Any normed field over ℝ is isomorphic as an ℝ-algebra to either ℝ (dim 1) or ℂ (dim 2).
Thus `finrank ℝ F ∈ {1, 2} ⊆ {1, 2, 4, 8}`.

**Non-commutative case** (A is a division ring): Requires additional machinery.
The classical proof proceeds via Clifford algebras and Radon-Hurwitz numbers:
1. Unit elements of A generate Clifford relations on ℝ^(dim A - 1)
2. Cl(n-1) has a real n-dimensional module only when n ∈ {1, 2, 4, 8}
   (Radon-Hurwitz numbers: ρ(n) forces this via the periodicity theorem)
3. Alternatively: reduce to `NSquareIdentity n` (HurwitzTheorem.lean) and
   apply the `hurwitz_only_if` axiom there.
Currently formalized as a sorry, pending Clifford representation theory in Mathlib.

## Relation to HurwitzTheorem.lean

The parent file `HurwitzTheorem.lean` contains:
  `axiom hurwitz_only_if (n : ℕ) (hn : n > 0) (nsi : NSquareIdentity n) :
    n ∈ admissibleDimensions`
for the `NSquareIdentity` formulation. This file works with `NormedDivisionRing`,
the Mathlib typeclass for (associative) normed division algebras. The two formulations
are mathematically equivalent; the reduction is:
  NormedDivisionRing A (dim n) → NSquareIdentity n
by choosing an orthonormal basis and transporting multiplication through coordinates.

## Key results

- `hurwitz_field_case`: proved (0 sorries) — Gelfand-Mazur for commutative algebras
- `minpoly_natDegree_le_two`, `exists_quadratic`: proved (0 sorries) — Frobenius Step 1
  (every element satisfies a real quadratic)
- `exists_real_shift_sq_scalar`, `eq_smul_one_of_sq_eq_nonneg_smul`: proved (0 sorries) —
  Frobenius Step 2 (completing the square; nonnegative square ⟹ real, so the imaginary
  part squares to a *negative* scalar)
- `anticommutator_real_affine`: proved (0 sorries) — Frobenius Step 3 preparation
  (`x*y + y*x ∈ span_ℝ {x, y, 1}` for all `x, y`, via polarisation of the Step-1 quadratics)
- `hurwitz_only_if_ring`: 1 sorry — the remaining global structure argument (Step 3:
  `Im A` is a subspace with a positive-definite bilinear form / Clifford structure)
-/

namespace HurwitzOnlyIf

open Module

/-! ### Admissible Dimensions -/

/-- The admissible dimensions for normed division algebras: {1, 2, 4, 8}. -/
def admissibleDimensions : Set ℕ := {1, 2, 4, 8}

/-! ### The Field (Commutative) Case via Gelfand-Mazur -/

/-- **Gelfand-Mazur consequence**: Any normed field over ℝ has finrank 1 or 2.
    Uses the Gelfand-Mazur theorem from Mathlib: every normed ℝ-algebra field
    is isomorphic to ℝ (yielding finrank 1) or ℂ (yielding finrank 2). -/
theorem finrank_normed_field_eq_one_or_two (F : Type*) [NormedField F] [NormedAlgebra ℝ F] :
    Module.finrank ℝ F = 1 ∨ Module.finrank ℝ F = 2 := by
  obtain h | h := NormedAlgebra.Real.nonempty_algEquiv_or F
  · -- Case: F ≅ ℝ as ℝ-algebra, so finrank ℝ F = finrank ℝ ℝ = 1
    obtain ⟨e⟩ := h
    exact Or.inl (e.toLinearEquiv.finrank_eq.trans (CommSemiring.finrank_self ℝ))
  · -- Case: F ≅ ℂ as ℝ-algebra, so finrank ℝ F = finrank ℝ ℂ = 2
    obtain ⟨e⟩ := h
    exact Or.inr (e.toLinearEquiv.finrank_eq.trans Complex.finrank_real_complex)

/-- **Hurwitz field case**: A normed field over ℝ has finrank in {1, 2, 4, 8}.
    This is the commutative subcase, fully proved via Gelfand-Mazur.
    No assumption of finite-dimensionality is needed: Gelfand-Mazur implies it. -/
theorem hurwitz_field_case (F : Type*) [NormedField F] [NormedAlgebra ℝ F] :
    Module.finrank ℝ F ∈ admissibleDimensions := by
  have h := finrank_normed_field_eq_one_or_two F
  simp only [admissibleDimensions, Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases h with h | h <;> omega

/-! ### Frobenius Step 1: Quadratic Minimal Polynomials

The associative case of Hurwitz's only-if direction is exactly **Frobenius' theorem**:
`NormedDivisionRing` is associative, so the octonions (dim 8) are excluded and the
answer is `{1, 2, 4}`. The classical proof of Frobenius begins by showing that every
element generates a subalgebra isomorphic to `ℝ` or `ℂ` — equivalently, every element
satisfies a real polynomial of degree at most two. The lemmas below establish this first
step, fully verified (0 sorries), for any finite-dimensional normed division ring over `ℝ`.

The remaining gap toward closing `hurwitz_only_if_ring` is the *global* structure argument:
split `A = ℝ ⬝ 1 ⊕ Im A` using these quadratics, equip `Im A` with the bilinear form
`⟨x, y⟩ = -(xy + yx)/2`, and analyze its dimension. That step is not yet formalized. -/

open Polynomial in
/-- **Frobenius Step 1a.** Every element of a finite-dimensional normed division ring over
`ℝ` has a minimal polynomial of natural degree at most two. Its minimal polynomial is
irreducible (the ambient ring is a domain and the element is integral), and irreducible
real polynomials have degree `≤ 2`. -/
theorem minpoly_natDegree_le_two (A : Type*) [NormedDivisionRing A] [NormedAlgebra ℝ A]
    [Module.Finite ℝ A] (a : A) : (minpoly ℝ a).natDegree ≤ 2 :=
  (minpoly.irreducible (IsIntegral.of_finite ℝ a)).natDegree_le_two

open Polynomial in
/-- **Frobenius Step 1b.** Every element `a` of a finite-dimensional normed division ring
over `ℝ` satisfies an explicit real quadratic relation `a ^ 2 = p • a + q • 1`. This is the
"each element generates `ℝ` or `ℂ`" heart of Frobenius' theorem, extracted directly from the
degree-`≤ 2` minimal polynomial. -/
theorem exists_quadratic (A : Type*) [NormedDivisionRing A] [NormedAlgebra ℝ A]
    [Module.Finite ℝ A] (a : A) : ∃ p q : ℝ, a ^ 2 = p • a + q • (1 : A) := by
  set m := minpoly ℝ a with hm
  have hint : IsIntegral ℝ a := IsIntegral.of_finite ℝ a
  have hmonic : m.Monic := minpoly.monic hint
  have hdeg : m.natDegree ≤ 2 := minpoly_natDegree_le_two A a
  have hpos : 0 < m.natDegree := minpoly.natDegree_pos hint
  have haeval : aeval a m = 0 := minpoly.aeval ℝ a
  -- Expand `aeval a m` over `range 3` (since `natDegree m ≤ 2 < 3`).
  have hexp : m.coeff 0 • (1 : A) + m.coeff 1 • a + m.coeff 2 • a ^ 2 = 0 := by
    have := aeval_eq_sum_range' (R := ℝ) (S := A) (p := m) (n := 3) (by omega) a
    rw [haeval] at this
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one] at this
    linear_combination (norm := module) -this
  interval_cases h : m.natDegree
  · -- `natDegree = 1`: monic ⟹ `coeff 1 = 1`, `coeff 2 = 0`, so `a = -coeff0 • 1`.
    have hc1 : m.coeff 1 = 1 := by
      have := hmonic.leadingCoeff; rwa [leadingCoeff, h] at this
    have hc2 : m.coeff 2 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hc1, hc2, one_smul, zero_smul, add_zero] at hexp
    have ha : a = (-m.coeff 0) • (1 : A) := by
      have : a = -(m.coeff 0 • (1 : A)) := by linear_combination (norm := module) hexp
      rw [this, neg_smul]
    exact ⟨-m.coeff 0, 0, by rw [sq, ha, smul_mul_assoc, one_mul, zero_smul, add_zero]⟩
  · -- `natDegree = 2`: monic ⟹ `coeff 2 = 1`.
    have hc2 : m.coeff 2 = 1 := by
      have := hmonic.leadingCoeff; rwa [leadingCoeff, h] at this
    rw [hc2, one_smul] at hexp
    exact ⟨-m.coeff 1, -m.coeff 0, by linear_combination (norm := module) hexp⟩

/-! ### Frobenius Step 2: Completing the Square and the Real/Imaginary Dichotomy

The quadratic relation `a ^ 2 = p • a + q • 1` of Step 1 can be *completed*: shifting `a`
by the real scalar `p / 2` produces an element whose square is a pure real scalar. This is
the concrete form of the classical decomposition `A = ℝ ⬝ 1 ⊕ Im A`. The sign of that scalar
then decides everything: a nonnegative scalar square forces the element back into `ℝ ⬝ 1`
(using that a division ring has no zero divisors), so the genuinely "imaginary" elements are
exactly those whose shifted square is a *negative* real scalar. These two lemmas are fully
verified (0 sorries) and set up the imaginary subspace `Im A`. -/

open Polynomial in
/-- **Frobenius Step 2a (completing the square).** For every element `a`, subtracting the
real scalar `p / 2` (half the linear coefficient of its quadratic) yields an element whose
square is a pure real scalar: `(a - c • 1) ^ 2 = r • 1`. This is the concrete form of the
`A = ℝ ⬝ 1 ⊕ Im A` splitting — `c • 1` is the real part and `a - c • 1` the imaginary part. -/
theorem exists_real_shift_sq_scalar (A : Type*) [NormedDivisionRing A] [NormedAlgebra ℝ A]
    [Module.Finite ℝ A] (a : A) : ∃ c r : ℝ, (a - c • (1 : A)) ^ 2 = r • (1 : A) := by
  obtain ⟨p, q, hpq⟩ := exists_quadratic A a
  refine ⟨p / 2, q + (p / 2) ^ 2, ?_⟩
  have hexp : (a - (p / 2) • (1 : A)) ^ 2
      = a * a - (2 * (p / 2)) • a + ((p / 2) ^ 2) • (1 : A) := by
    simp only [sq, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, one_mul, mul_one]
    module
  rw [hexp, ← pow_two, hpq]
  module

/-- **Frobenius Step 2b (nonnegative square ⟹ real).** If an element `b` of a normed
division ring satisfies `b ^ 2 = r • 1` with `r ≥ 0`, then `b` is a real scalar multiple of
`1`. Indeed `(b - √r • 1)(b + √r • 1) = b ^ 2 - r • 1 = 0`, and a division ring has no zero
divisors, so one factor vanishes. Consequently the "imaginary part" `a - c • 1` from Step 2a
is genuinely non-real only when its square scalar `r` is *negative*. -/
theorem eq_smul_one_of_sq_eq_nonneg_smul (A : Type*) [NormedDivisionRing A]
    [NormedAlgebra ℝ A] (b : A) (r : ℝ) (hr : 0 ≤ r) (hb : b ^ 2 = r • (1 : A)) :
    ∃ s : ℝ, b = s • (1 : A) := by
  set s := Real.sqrt r with hs
  have hs2 : s ^ 2 = r := Real.sq_sqrt hr
  have factored : (b - s • (1 : A)) * (b + s • (1 : A)) = 0 := by
    have hexp : (b - s • (1 : A)) * (b + s • (1 : A)) = b * b - (s ^ 2) • (1 : A) := by
      simp only [mul_add, sub_mul, mul_smul_comm, smul_mul_assoc, one_mul, mul_one]
      module
    rw [hexp, ← pow_two, hb, hs2]
    module
  rcases mul_eq_zero.mp factored with h | h
  · exact ⟨s, by linear_combination (norm := module) h⟩
  · exact ⟨-s, by linear_combination (norm := module) h⟩

/-! ### Frobenius Step 3 preparation: the anticommutator is real-affine

The Clifford structure that pins `finrank ℝ (Im A)` down begins with a single algebraic
constraint on the anticommutator `x*y + y*x`.  The following lemma is the first honest step
towards it and is fully verified: applying the Step-1 quadratic relation to `x`, `y` and
`x + y` and polarising (`(x+y)² = x² + (xy+yx) + y²`) expresses the anticommutator as a
*real-linear* combination of `x`, `y` and `1`.  Equivalently, `x*y + y*x ∈ span_ℝ {x, y, 1}`
for all `x, y` — no commutativity assumed.  This is exactly the algebra that, once restricted
to imaginary `x, y` (where the `x` and `y` coefficients drop out by trace-additivity), yields
the scalar-valued anticommutator `x*y + y*x ∈ ℝ•1` underpinning the Clifford relations. -/
theorem anticommutator_real_affine (A : Type*) [NormedDivisionRing A] [NormedAlgebra ℝ A]
    [Module.Finite ℝ A] (x y : A) :
    ∃ c₁ c₂ c₃ : ℝ, x * y + y * x = c₁ • x + c₂ • y + c₃ • (1 : A) := by
  obtain ⟨px, qx, hx⟩ := exists_quadratic A x
  obtain ⟨py, qy, hy⟩ := exists_quadratic A y
  obtain ⟨ps, qs, hs⟩ := exists_quadratic A (x + y)
  refine ⟨ps - px, ps - py, qs - qx - qy, ?_⟩
  -- polarisation: (x + y)² = x² + (xy + yx) + y²
  have hpol : (x + y) ^ 2 = x ^ 2 + (x * y + y * x) + y ^ 2 := by
    simp only [pow_two]; noncomm_ring
  -- rewrite each square by its Step-1 quadratic and read off the coefficients
  have key : x ^ 2 + (x * y + y * x) + y ^ 2 = ps • (x + y) + qs • (1 : A) := by
    rw [← hpol]; exact hs
  rw [hx, hy] at key
  linear_combination (norm := module) key

/-! ### Frobenius Step 3: the imaginary subspace and its scalar anticommutator

Step 2 splits `A = ℝ ⬝ 1 ⊕ Im A`, where the *imaginary* elements are those whose square
is a nonpositive real scalar. Two facts pin the Clifford structure down:

* the sum is **direct** — a real multiple of `1` is imaginary only if it is `0`
  (`eq_zero_of_smul_one_sq_nonpos` / `isImaginary_smul_one_iff`), and
* the **anticommutator is scalar** — whenever `x²`, `y²` and `(x+y)²` are all real
  scalars, `x*y + y*x` is the real scalar `(c - a - b) ⬝ 1`
  (`anticommutator_scalar_of_sq_scalar`), the exact Clifford relation `eᵢeⱼ + eⱼeᵢ ∈ ℝ⬝1`.

Both are fully verified below. The one remaining global step is that `Im A` is closed
under addition (equivalently, the real-part functional `A → ℝ` is `ℝ`-linear), which
supplies the hypothesis `(x+y)² = c ⬝ 1` for imaginary `x, y` and turns the scalar
anticommutator into a genuine positive-definite bilinear form, forcing
`finrank ℝ (Im A) ∈ {0, 1, 3}`. -/

/-- **Imaginary elements.** `a` is *imaginary* when its square is a nonpositive real
scalar, `a² = r ⬝ 1` with `r ≤ 0`. Zero is imaginary (`r = 0`); by Step 2b
(`eq_smul_one_of_sq_eq_nonneg_smul`) a nonzero imaginary element is never a real
multiple of `1`, so `ℝ ⬝ 1 ∩ Im A = {0}`. -/
def IsImaginary (A : Type*) [NormedDivisionRing A] [NormedAlgebra ℝ A] (a : A) : Prop :=
  ∃ r : ℝ, r ≤ 0 ∧ a ^ 2 = r • (1 : A)

/-- **Directness of `A = ℝ ⬝ 1 ⊕ Im A`.** A real multiple `s ⬝ 1` whose square is a
nonpositive real scalar must be zero: `(s ⬝ 1)² = s² ⬝ 1` with `s² ≥ 0`, and the injective
`algebraMap ℝ A` forces `s² = r ≤ 0`, hence `s = 0`. -/
theorem eq_zero_of_smul_one_sq_nonpos (A : Type*) [NormedDivisionRing A] [NormedAlgebra ℝ A]
    (s r : ℝ) (hr : r ≤ 0) (h : (s • (1 : A)) ^ 2 = r • (1 : A)) : s = 0 := by
  have hexp : (s • (1 : A)) ^ 2 = (s * s) • (1 : A) := by
    rw [sq, smul_mul_smul_comm, mul_one]
  rw [hexp] at h
  have hinj : Function.Injective (algebraMap ℝ A) := RingHom.injective _
  have hval : s * s = r := by
    apply hinj
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]; exact h
  have : s * s = 0 := le_antisymm (hval.le.trans hr) (mul_self_nonneg s)
  exact mul_self_eq_zero.mp this

/-- The imaginary elements meet the reals only at `0`: `s ⬝ 1` is imaginary iff `s = 0`. -/
theorem isImaginary_smul_one_iff (A : Type*) [NormedDivisionRing A] [NormedAlgebra ℝ A]
    (s : ℝ) : IsImaginary A (s • (1 : A)) ↔ s = 0 := by
  constructor
  · rintro ⟨r, hr, h⟩; exact eq_zero_of_smul_one_sq_nonpos A s r hr h
  · rintro rfl; exact ⟨0, le_refl 0, by simp⟩

/-- **The scalar anticommutator (Clifford relation).** If the three squares `x²`, `y²`
and `(x+y)²` are real scalars `a ⬝ 1`, `b ⬝ 1`, `c ⬝ 1`, then the anticommutator is the
real scalar `(c - a - b) ⬝ 1`. This is pure polarisation of the square,
`(x+y)² = x² + (x*y + y*x) + y²`; no division-ring hypothesis beyond the ambient algebra
is used. For imaginary `x, y` it is exactly the Clifford relation `x*y + y*x ∈ ℝ ⬝ 1`. -/
theorem anticommutator_scalar_of_sq_scalar (A : Type*) [NormedDivisionRing A]
    [NormedAlgebra ℝ A] (x y : A) (a b c : ℝ)
    (hx : x ^ 2 = a • (1 : A)) (hy : y ^ 2 = b • (1 : A))
    (hxy : (x + y) ^ 2 = c • (1 : A)) :
    x * y + y * x = (c - a - b) • (1 : A) := by
  have hpol : (x + y) ^ 2 = x ^ 2 + (x * y + y * x) + y ^ 2 := by
    simp only [pow_two]; noncomm_ring
  rw [hx, hy, hxy] at hpol
  linear_combination (norm := module) -hpol

/-! ### Frobenius Step 3: the keystone — imaginary anticommutators are scalar

The last global obstruction to `Im A` being an `ℝ`-subspace is that the anticommutator
`x*y + y*x` of two *imaginary* elements is a real scalar.  The classical proof of this fact
runs a linear-independence case split on `{1, x, y}`.  The lemma below discharges it by a
short, wholly computational route that needs no such split:

* Completing the square on `x + y` (`exists_real_shift_sq_scalar`) gives
  `x*y + y*x = (2c) • (x + y) + μ • 1`.
* Multiplying that identity by `x` on the left and on the right yields the *same* element
  (because `x² = a • 1` is central), so the two expansions must agree — which forces
  `(2c) • (x*y - y*x) = 0` in the `ℝ`-vector space `A`.
* Hence either `c = 0`, in which case the identity already reads `x*y + y*x = μ • 1`; or
  `x*y = y*x`, in which case `(x*y)² = x² y² = (a·b) • 1` with `a·b ≥ 0`, so Step 2b
  (`eq_smul_one_of_sq_eq_nonneg_smul`) makes `x*y` itself a real scalar and therefore so is
  `x*y + y*x = 2·(x*y)`.

This is the exact Clifford relation `eᵢeⱼ + eⱼeᵢ ∈ ℝ ⬝ 1`; it upgrades the scalar
anticommutator of `anticommutator_scalar_of_sq_scalar` from a *hypothesis* to a *theorem* for
imaginary inputs, giving a well-defined symmetric bilinear form on `Im A`. -/
theorem anticommutator_scalar_imaginary (A : Type*) [NormedDivisionRing A] [NormedAlgebra ℝ A]
    [Module.Finite ℝ A] {x y : A} (hx : IsImaginary A x) (hy : IsImaginary A y) :
    ∃ t : ℝ, x * y + y * x = t • (1 : A) := by
  obtain ⟨a, ha, hxsq⟩ := hx
  obtain ⟨b, hb, hysq⟩ := hy
  -- Complete the square on `x + y`: `(x + y)² = (2c)•(x + y) + (r - c²)•1`.
  obtain ⟨c, r, hc⟩ := exists_real_shift_sq_scalar A (x + y)
  have hsum_sq : (x + y) ^ 2 = (2 * c) • (x + y) + (r - c ^ 2) • (1 : A) := by
    have hexp : ((x + y) - c • (1 : A)) ^ 2
        = (x + y) * (x + y) - (2 * c) • (x + y) + (c ^ 2) • (1 : A) := by
      simp only [sq, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, one_mul, mul_one]
      module
    rw [hexp, ← pow_two] at hc
    linear_combination (norm := module) hc
  -- Polarisation: `(x + y)² = x² + (x*y + y*x) + y²`.
  have hpol : (x + y) ^ 2 = x ^ 2 + (x * y + y * x) + y ^ 2 := by
    simp only [pow_two]; noncomm_ring
  set μ : ℝ := r - c ^ 2 - a - b with hμ
  -- Solve for the anticommutator: `x*y + y*x = (2c)•(x + y) + μ•1`.
  have hS : x * y + y * x = (2 * c) • (x + y) + μ • (1 : A) := by
    rw [hpol, hxsq, hysq] at hsum_sq
    rw [hμ]; linear_combination (norm := module) hsum_sq
  by_cases hc0 : c = 0
  · -- `c = 0`: the identity already exhibits the anticommutator as the scalar `μ`.
    exact ⟨μ, by rw [hS, hc0]; simp⟩
  · -- `c ≠ 0`: multiplying `hS` by `x` on both sides forces `x` and `y` to commute.
    have h2c : (2 * c) ≠ 0 := mul_ne_zero two_ne_zero hc0
    have hcomm0 : (2 * c) • (x * y - y * x) = 0 := by
      have hLR : x * (x * y + y * x) = (x * y + y * x) * x := by
        have h1 : x * (x * y + y * x) = x ^ 2 * y + x * y * x := by rw [pow_two]; noncomm_ring
        have h2 : (x * y + y * x) * x = x * y * x + y * x ^ 2 := by rw [pow_two]; noncomm_ring
        rw [h1, h2, hxsq]
        simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
        abel
      have hLexp : x * (x * y + y * x)
          = (2 * c) • (x * x) + (2 * c) • (x * y) + μ • x := by
        rw [hS]; simp only [mul_add, mul_smul_comm, mul_one]; module
      have hRexp : (x * y + y * x) * x
          = (2 * c) • (x * x) + (2 * c) • (y * x) + μ • x := by
        rw [hS]; simp only [add_mul, smul_mul_assoc, one_mul]; module
      rw [hLexp, hRexp] at hLR
      have hxyeq : (2 * c) • (x * y) = (2 * c) • (y * x) := by
        linear_combination (norm := module) hLR
      rw [smul_sub, hxyeq]; exact sub_self _
    have hxy0 : x * y - y * x = 0 := by
      have e : x * y - y * x = (2 * c)⁻¹ • ((2 * c) • (x * y - y * x)) := by
        rw [smul_smul, inv_mul_cancel₀ h2c, one_smul]
      rw [e, hcomm0, smul_zero]
    have hxyc : x * y = y * x := sub_eq_zero.mp hxy0
    -- Commuting imaginaries: `(x*y)² = x²y² = (a·b)•1` with `a·b ≥ 0`, so `x*y` is scalar.
    have hab : (0 : ℝ) ≤ a * b := by
      have := mul_nonneg (neg_nonneg.2 ha) (neg_nonneg.2 hb); simpa using this
    have hsq : (x * y) ^ 2 = (a * b) • (1 : A) := by
      have hxy2 : (x * y) ^ 2 = x ^ 2 * y ^ 2 := by
        simp only [pow_two]
        calc x * y * (x * y) = x * (y * x) * y := by noncomm_ring
          _ = x * (x * y) * y := by rw [hxyc]
          _ = x * x * (y * y) := by noncomm_ring
      rw [hxy2, hxsq, hysq, smul_mul_smul_comm, mul_one]
    obtain ⟨s, hs⟩ := eq_smul_one_of_sq_eq_nonneg_smul A (x * y) (a * b) hab hsq
    exact ⟨2 * s, by rw [← hxyc, hs]; module⟩

/-- **`Im A` is closed under addition.** For imaginary `x, y`, the sum `x + y` is imaginary:
its square is a nonpositive real scalar. Together with closure under real scalars and
containment of `0`, this makes `Im A` an `ℝ`-subspace — the last structural fact this file
needed for the Clifford / bilinear-form argument, and the blocker in the problem's research
log ("`Im A` closed under addition ⟺ the real-part functional `A → ℝ` is `ℝ`-linear").

The square is scalar by polarisation and the keystone `anticommutator_scalar_imaginary`:
`(x + y)² = x² + (x*y + y*x) + y² = (a + b + t)•1`. Nonpositivity of `a + b + t` is forced:
were it positive, Step 2b (`eq_smul_one_of_sq_eq_nonneg_smul`) would put `x + y ∈ ℝ•1`, and
the completing-the-square relation `(2s)•x = (s² + a - b)•1` would collapse `x` (hence, by
symmetry, `y`) into `ℝ•1 ∩ Im A = {0}` (`isImaginary_smul_one_iff`), contradicting `s ≠ 0`. -/
theorem isImaginary_add (A : Type*) [NormedDivisionRing A] [NormedAlgebra ℝ A]
    [Module.Finite ℝ A] {x y : A} (hx : IsImaginary A x) (hy : IsImaginary A y) :
    IsImaginary A (x + y) := by
  obtain ⟨t, ht⟩ := anticommutator_scalar_imaginary A hx hy
  obtain ⟨a, ha, hxsq⟩ := hx
  obtain ⟨b, hb, hysq⟩ := hy
  -- `(x + y)² = (a + b + t)•1`.
  have hsum : (x + y) ^ 2 = (a + b + t) • (1 : A) := by
    have hpol : (x + y) ^ 2 = x ^ 2 + (x * y + y * x) + y ^ 2 := by
      simp only [pow_two]; noncomm_ring
    rw [hpol, hxsq, hysq, ht]; module
  refine ⟨a + b + t, ?_, hsum⟩
  by_contra hpos
  push_neg at hpos   -- `hpos : 0 < a + b + t`
  obtain ⟨s, hs⟩ := eq_smul_one_of_sq_eq_nonneg_smul A (x + y) (a + b + t) hpos.le hsum
  -- Completing the square on `y = s•1 - x` gives `(2s)•x = (s² + a - b)•1`.
  have hrel : (2 * s) • x = (s ^ 2 + a - b) • (1 : A) := by
    have hy_eq : y = s • (1 : A) - x := by rw [← hs]; abel
    have he : y ^ 2 = (s ^ 2 + a) • (1 : A) - (2 * s) • x := by
      rw [hy_eq]
      have hexp : (s • (1 : A) - x) ^ 2
          = (s ^ 2) • (1 : A) - (2 * s) • x + x * x := by
        simp only [sq, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, one_mul, mul_one]
        module
      rw [hexp, ← pow_two, hxsq]; module
    rw [hysq] at he
    linear_combination (norm := module) he
  rcases eq_or_ne s 0 with hs0 | hs0
  · -- `s = 0` ⟹ `x + y = 0` ⟹ `(a + b + t)•1 = 0` ⟹ `a + b + t = 0`, contradiction.
    rw [hs0, zero_smul] at hs
    rw [hs, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsum
    have hinj : Function.Injective (algebraMap ℝ A) := RingHom.injective _
    have hk : a + b + t = 0 := by
      apply hinj
      rw [map_zero, Algebra.algebraMap_eq_smul_one]; exact hsum.symm
    exact absurd hk (ne_of_gt hpos)
  · -- `s ≠ 0` ⟹ `x` is a real scalar, hence `0`; then `y = s•1` imaginary forces `s = 0`.
    have h2s : (2 * s) ≠ 0 := mul_ne_zero two_ne_zero hs0
    set k : ℝ := (2 * s)⁻¹ * (s ^ 2 + a - b) with hk
    have hx_real : x = k • (1 : A) := by
      have e : x = (2 * s)⁻¹ • ((2 * s) • x) := by
        rw [smul_smul, inv_mul_cancel₀ h2s, one_smul]
      rw [e, hrel, smul_smul, hk]
    have hkimg : IsImaginary A (k • (1 : A)) := by rw [← hx_real]; exact ⟨a, ha, hxsq⟩
    have hx0 : x = 0 := by
      rw [hx_real, (isImaginary_smul_one_iff A k).mp hkimg, zero_smul]
    have hy_real : y = s • (1 : A) := by
      have hxy := hs; rw [hx0, zero_add] at hxy; exact hxy
    have hyimg : IsImaginary A (s • (1 : A)) := by rw [← hy_real]; exact ⟨b, hb, hysq⟩
    exact hs0 ((isImaginary_smul_one_iff A s).mp hyimg)

/-! ### The General (Division Ring) Case -/

/-- **Frobenius Step 3, commutative subcase — fully verified.** If a normed division ring
`A` over `ℝ` is *commutative*, then it is a normed field, so Gelfand–Mazur
(`hurwitz_field_case`) pins `finrank ℝ A ∈ {1, 2} ⊆ admissibleDimensions`. This discharges
the easy half of the case split in `hurwitz_only_if_ring`, leaving only the genuinely
non-commutative case (the Clifford / Radon–Hurwitz argument) open. No finite-dimensionality
hypothesis is needed — Gelfand–Mazur supplies it. -/
theorem hurwitz_only_if_ring_comm (A : Type*) [NormedDivisionRing A] [NormedAlgebra ℝ A]
    (hcomm : ∀ x y : A, x * y = y * x) :
    Module.finrank ℝ A ∈ admissibleDimensions := by
  letI : NormedField A := { ‹NormedDivisionRing A› with mul_comm := hcomm }
  exact hurwitz_field_case A

/-- **Hurwitz Only-If for Normed Division Rings**:
    A finite-dimensional normed division ring over ℝ has finrank in {1, 2, 4, 8}.

    **Commutative subcase**: If A is also a field (commutative), this follows from
    `hurwitz_field_case` (proved via Gelfand-Mazur).

    **Non-commutative subcase** (HARD sorry): The classical proof uses Clifford algebras.
    For a normed division ring A of dimension n, the (n-1) imaginary unit vectors satisfy
    Clifford relations: eᵢeⱼ + eⱼeᵢ = -2δᵢⱼ, giving a real representation of Cl(n-1).
    The Radon-Hurwitz numbers force n ∈ {1, 2, 4, 8}.

    Alternative: reduce to `HurwitzTheorem.NSquareIdentity n` via an orthonormal basis
    construction, then apply `HurwitzTheorem.hurwitz_only_if` (axiom in that file).

    **Frobenius' theorem** (associative case): For associative division algebras over ℝ,
    the only possibilities are ℝ (dim 1), ℂ (dim 2), ℍ (dim 4). Octonions (dim 8) are
    non-associative and require a separate argument beyond `NormedDivisionRing`. -/
theorem hurwitz_only_if_ring (A : Type*) [NormedDivisionRing A] [NormedAlgebra ℝ A]
    [Module.Finite ℝ A] :
    Module.finrank ℝ A ∈ admissibleDimensions := by
  /- Proof outline (Frobenius' theorem, since `NormedDivisionRing` is associative so the
     answer is in fact `{1, 2, 4} ⊆ {1, 2, 4, 8}`):
     STEP 1 (VERIFIED above): every `a : A` satisfies a real quadratic `a² = p•a + q•1`
       via `exists_quadratic` / `minpoly_natDegree_le_two`. Hence each element generates a
       subalgebra isomorphic to `ℝ` or `ℂ`.
     STEP 2a (VERIFIED above): completing the square, `(a - (p/2)•1)² = r•1` for a real
       scalar `r` (`exists_real_shift_sq_scalar`). This is the concrete `A = ℝ•1 ⊕ Im A`
       shift: `(p/2)•1` is the real part, `a - (p/2)•1` the imaginary part.
     STEP 2b (VERIFIED above): if `b² = r•1` with `r ≥ 0` then `b ∈ ℝ•1`
       (`eq_smul_one_of_sq_eq_nonneg_smul`, from the absence of zero divisors). So the
       imaginary part is genuinely non-real exactly when its square scalar `r` is negative,
       pinning down `Im A := {a | a² ∈ ℝ≤0 • 1}`.
     STEP 3 (partially VERIFIED above): the `A = ℝ•1 ⊕ Im A` decomposition is now direct
       (`eq_zero_of_smul_one_sq_nonpos` / `isImaginary_smul_one_iff`: `ℝ•1 ∩ Im A = {0}`),
       and the Clifford relation `x*y + y*x = (c-a-b)•1 ∈ ℝ•1` is verified whenever the
       three squares `x², y², (x+y)²` are real scalars (`anticommutator_scalar_of_sq_scalar`).
       What REMAINS is the single global fact that `Im A` is closed under addition
       (equivalently the real-part functional `A → ℝ` is `ℝ`-linear); this supplies the
       missing hypothesis `(x+y)² ∈ ℝ•1` for imaginary `x, y`, upgrading the scalar
       anticommutator to a positive-definite symmetric bilinear form and forcing
       `finrank ℝ (Im A) ∈ {0, 1, 3}`, hence `finrank ℝ A ∈ {1, 2, 4}`.
     Step 3's closure-of-`Im A` step is not yet formalized; Mathlib lacks the
     Clifford-algebra / bilinear-form machinery to discharge it directly.

     The commutative branch of Step 3 is now fully verified (`hurwitz_only_if_ring_comm`
     via Gelfand–Mazur), so the sorry below is scoped to the *strictly non-commutative*
     case — where `hnc : ∃ x y, x * y ≠ y * x` is available as a genuine hypothesis. -/
  by_cases hcomm : ∀ x y : A, x * y = y * x
  · -- Commutative subcase: A is a normed field, closed by Gelfand–Mazur.
    exact hurwitz_only_if_ring_comm A hcomm
  · -- Non-commutative subcase: the Clifford / Radon–Hurwitz argument (still open).
    push_neg at hcomm
    obtain ⟨x, y, _hxy⟩ := hcomm
    sorry

end HurwitzOnlyIf
