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

/-! ### Frobenius Step 3: the imaginary subspace `Im A` is well-defined

Completing the square (Step 2) singles out the *imaginary* elements — those whose square is a
nonpositive real scalar. The lemmas below are the structural backbone of the decomposition
`A = ℝ • 1 ⊕ Im A` (0 new sorries; ⚠️ build verification pending — the Docker/containerd
toolchain was unavailable at authoring time, so these proofs are hand-audited but not yet
machine-checked):

* `isImaginary_zero`, `eq_zero_of_isImaginary_of_isReal`: `Im A ∩ ℝ • 1 = {0}`.
* `exists_isImaginary_sub_smul` **and** `isImaginary_sub_smul_unique`: every `a : A` has a
  *unique* real part `c` with `a - c • 1 ∈ Im A`. Together these make the projection
  `re : A → ℝ` well-defined — the next Step-3 milestone (proving `re` is `ℝ`-linear, so
  `Im A = ker re` is a subspace) builds directly on this. -/

/-- An element of a normed division ring is **imaginary** when its square is a nonpositive
real scalar multiple of `1`. Genuinely imaginary elements (square scalar `< 0`) lie outside
`ℝ • 1`; the only imaginary real scalar is `0`. This is the concrete `Im A` from the
`A = ℝ • 1 ⊕ Im A` decomposition, cut out by the sign dichotomy of Frobenius Step 2. -/
def IsImaginary (A : Type*) [NormedDivisionRing A] [NormedAlgebra ℝ A] (a : A) : Prop :=
  ∃ r : ℝ, r ≤ 0 ∧ a ^ 2 = r • (1 : A)

/-- `0` is imaginary: its square is `0 = 0 • 1` and `0 ≤ 0`. -/
theorem isImaginary_zero (A : Type*) [NormedDivisionRing A] [NormedAlgebra ℝ A] :
    IsImaginary A (0 : A) :=
  ⟨0, le_refl 0, by simp⟩

/-- **`Im A ∩ ℝ • 1 = {0}`.** An imaginary element that is also a real scalar multiple of `1`
must be `0`: writing `a = s • 1` gives `a ^ 2 = s ^ 2 • 1`, so the imaginary scalar equals
`s ^ 2 ≥ 0`; combined with `≤ 0` this forces `s = 0`. Uses that `ℝ` acts without zero
divisors on `A` (`smul_eq_zero`, `one_ne_zero`) and `s ^ 2 = 0 ⟹ s = 0`. -/
theorem eq_zero_of_isImaginary_of_isReal (A : Type*) [NormedDivisionRing A] [NormedAlgebra ℝ A]
    (a : A) (hi : IsImaginary A a) (s : ℝ) (hs : a = s • (1 : A)) : a = 0 := by
  obtain ⟨r, hr_le, hr_eq⟩ := hi
  have h1 : a ^ 2 = (s ^ 2) • (1 : A) := by
    rw [hs, pow_two, smul_mul_assoc, one_mul, smul_smul, ← pow_two]
  have h2 : (s ^ 2 - r) • (1 : A) = 0 := by
    rw [sub_smul, ← h1, hr_eq, sub_self]
  have h3 : s ^ 2 - r = 0 := by
    rcases smul_eq_zero.mp h2 with h | h
    · exact h
    · exact absurd h one_ne_zero
  have h4 : s ^ 2 = r := by linarith
  have h5 : s = 0 := by
    have hsq0 : s ^ 2 = 0 := by linarith [sq_nonneg s]
    exact sq_eq_zero_iff.mp hsq0
  rw [hs, h5, zero_smul]

/-- **Real part exists.** Every `a : A` admits a real scalar `c` with `a - c • 1 ∈ Im A`.
From completing the square (`exists_real_shift_sq_scalar`) we get `(a - c₀ • 1) ^ 2 = r • 1`; if
`r ≤ 0` this is already imaginary, and if `r > 0` then Step 2b puts `a - c₀ • 1 ∈ ℝ • 1`, so
absorbing that scalar makes the imaginary part exactly `0`. -/
theorem exists_isImaginary_sub_smul (A : Type*) [NormedDivisionRing A] [NormedAlgebra ℝ A]
    [Module.Finite ℝ A] (a : A) : ∃ c : ℝ, IsImaginary A (a - c • (1 : A)) := by
  obtain ⟨c, r, hcr⟩ := exists_real_shift_sq_scalar A a
  rcases le_or_lt r 0 with hr | hr
  · exact ⟨c, r, hr, hcr⟩
  · obtain ⟨s, hs⟩ := eq_smul_one_of_sq_eq_nonneg_smul A (a - c • (1 : A)) r (le_of_lt hr) hcr
    refine ⟨c + s, ?_⟩
    have hzero : a - (c + s) • (1 : A) = 0 := by
      rw [add_smul, sub_add_eq_sub_sub, hs, sub_self]
    rw [hzero]
    exact isImaginary_zero A

/-- **Real part is unique.** If `a - c • 1` and `a - c' • 1` are both imaginary, then `c = c'`.
Writing `d = c' - c`, expanding `(a - c' • 1) ^ 2 = (a - c • 1) ^ 2 - (2d) • (a - c • 1) + d² • 1`
and using both square-scalar hypotheses gives `(2d) • (a - c • 1) ∈ ℝ • 1`; if `d ≠ 0` this puts
the imaginary element `a - c • 1` into `ℝ • 1`, forcing it to `0` by
`eq_zero_of_isImaginary_of_isReal`, whence `a - c' • 1 = (c - c') • 1 ∈ ℝ • 1` is likewise `0`,
so `c = c'`. Together with `exists_isImaginary_sub_smul` this makes `re : A → ℝ` well-defined. -/
theorem isImaginary_sub_smul_unique (A : Type*) [NormedDivisionRing A] [NormedAlgebra ℝ A]
    (a : A) (c c' : ℝ) (h : IsImaginary A (a - c • (1 : A)))
    (h' : IsImaginary A (a - c' • (1 : A))) : c = c' := by
  by_contra hne
  obtain ⟨r, _hr_le, hr_eq⟩ := h
  obtain ⟨r', _hr'_le, hr'_eq⟩ := h'
  set d := c' - c with hd_def
  have hd : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hu'_eq : a - c' • (1 : A) = (a - c • (1 : A)) - d • (1 : A) := by
    rw [hd_def, sub_smul]; abel
  have hkey : (2 * d) • (a - c • (1 : A)) = (r + d ^ 2 - r') • (1 : A) := by
    have expand : (a - c' • (1 : A)) ^ 2
        = (a - c • (1 : A)) * (a - c • (1 : A)) - (2 * d) • (a - c • (1 : A))
            + (d ^ 2) • (1 : A) := by
      rw [hu'_eq]
      simp only [sq, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, one_mul, mul_one]
      module
    rw [← pow_two] at expand
    rw [hr'_eq, hr_eq] at expand
    linear_combination (norm := module) expand
  have h2d : (2 * d) ≠ 0 := mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hd
  have hu_real : a - c • (1 : A) = ((r + d ^ 2 - r') / (2 * d)) • (1 : A) := by
    have hinv : a - c • (1 : A) = (2 * d)⁻¹ • ((2 * d) • (a - c • (1 : A))) := by
      rw [inv_smul_smul₀ h2d]
    rw [hinv, hkey, smul_smul, div_eq_inv_mul]
  have hu0 : a - c • (1 : A) = 0 :=
    eq_zero_of_isImaginary_of_isReal A (a - c • (1 : A)) ⟨r, _hr_le, hr_eq⟩ _ hu_real
  have ha : a = c • (1 : A) := by rw [sub_eq_zero] at hu0; exact hu0
  have hu'_real : a - c' • (1 : A) = (c - c') • (1 : A) := by rw [ha, ← sub_smul]
  have hu'0 : a - c' • (1 : A) = 0 :=
    eq_zero_of_isImaginary_of_isReal A (a - c' • (1 : A)) ⟨r', _hr'_le, hr'_eq⟩ (c - c') hu'_real
  rw [hu'_real] at hu'0
  have hcc : c - c' = 0 := by
    rcases smul_eq_zero.mp hu'0 with h1 | h1
    · exact h1
    · exact absurd h1 one_ne_zero
  exact hne (sub_eq_zero.mp hcc)

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
     STEP 3 (remaining): showing `Im A` is an ℝ-subspace (equivalently, that `x*y + y*x ∈
       ℝ•1` for imaginary `x, y`) and that `(x, y) ↦ -(x*y + y*x)` is a positive-definite
       symmetric bilinear form; multiplication then makes `Im A` a Clifford-type space,
       forcing `finrank ℝ (Im A) ∈ {0, 1, 3}` and thus `finrank ℝ A ∈ {1, 2, 4}`.
     Step 3 (the global structure/bilinear-form argument) is not yet formalized; Mathlib
     lacks the Clifford-algebra / bilinear-form machinery to discharge it directly.

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
