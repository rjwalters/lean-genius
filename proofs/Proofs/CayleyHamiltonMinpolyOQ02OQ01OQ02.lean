/-
  Characterizing Minpoly Invariance Under Non-Injective Algebra Maps
  (cayley-hamilton-minpoly-oq-02-oq-01-oq-02)

  Open Question: Can we characterize EXACTLY when minpoly is invariant under
  non-injective K-algebra homomorphisms?

  **Background** (from OQ02OQ01): For INJECTIVE f : A →ₐ[K] B, Mathlib's
  `minpoly.algHom_eq` gives `minpoly K (f a) = minpoly K a`. For NON-INJECTIVE
  f this can fail: the zero map sends everything to 0, so minpoly K (f a) = X.

  **Main Result (0 sorries)**:

    minpoly K (f a) = minpoly K a  ↔  Polynomial.aeval a (minpoly K (f a)) = 0

  This is a COMPLETE characterization: the minimal polynomial is preserved
  iff the (generally smaller) minimal polynomial of f(a) still vanishes at a.

  **Proof key**:
  - Always: minpoly(f a) ∣ minpoly(a)  [aeval_algHom + minpoly.dvd]
  - For equality: aeval a (minpoly(f a)) = 0 gives minpoly(a) ∣ minpoly(f a)
  - Mutual divisibility + both monic = equality  [eq_of_monic_of_associated]

  ## Axioms: 0  |  Sorries: 0
-/

import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Associated.Basic
import Mathlib.Tactic

open Polynomial minpoly

namespace MinpolyNonInjectiveChar

variable {K : Type*} [Field K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]

-- ============================================================================
-- Part I: Universal Divisibility (Always Holds, Regardless of Injectivity)
-- ============================================================================

/-- **Universal divisibility**: minpoly K (f a) always divides minpoly K a.

    Proof: f(minpoly(a)(a)) = minpoly(a)(f(a)) = 0 (algebra map + minpoly.aeval),
    so minpoly(f(a)) divides minpoly(a) by definition of minimal polynomial. -/
theorem minpoly_dvd_algHom (f : A →ₐ[K] B) (a : A) :
    minpoly K (f a) ∣ minpoly K a :=
  minpoly.dvd K (f a) (minpoly.aeval_algHom f a)

-- ============================================================================
-- Part II: The Exact Characterization
-- ============================================================================

/-- **Main Theorem** (answer to OQ-02-OQ-01-OQ-02):

    minpoly K (f a) = minpoly K a  ↔  Polynomial.aeval a (minpoly K (f a)) = 0

    **Intuition**: minpoly(f a) always divides minpoly(a) (the universal direction).
    Equality holds precisely when this divisibility goes BOTH ways — i.e., minpoly(f a)
    also divides minpoly(a) in the other direction — which happens iff aeval a = 0.

    **Proof (⟹)**: minpoly(f a) = minpoly(a), so aeval a (minpoly(f a)) = aeval a (minpoly(a)) = 0.

    **Proof (⟸)**: Given aeval a (minpoly(f a)) = 0:
    1. minpoly(f a) ∣ minpoly(a)   [universal, minpoly_dvd_algHom]
    2. minpoly(a) ∣ minpoly(f a)   [from assumption, minpoly.dvd]
    3. Both monic → equal          [eq_of_monic_of_associated + associated_of_dvd_dvd] -/
theorem minpoly_eq_iff_aeval_zero (f : A →ₐ[K] B) (a : A)
    (ha : IsIntegral K a) (hfa : IsIntegral K (f a)) :
    minpoly K (f a) = minpoly K a ↔
    Polynomial.aeval a (minpoly K (f a)) = 0 := by
  constructor
  · intro h
    rw [h]; exact minpoly.aeval K a
  · intro h
    have hdvd1 : minpoly K (f a) ∣ minpoly K a := minpoly_dvd_algHom f a
    have hdvd2 : minpoly K a ∣ minpoly K (f a) := minpoly.dvd K a h
    exact Polynomial.eq_of_monic_of_associated
      (minpoly.monic hfa)
      (minpoly.monic ha)
      (associated_of_dvd_dvd hdvd1 hdvd2)

/-- **Equivalent form** using `IsRoot`: minpoly K (f a) = minpoly K a iff
    a is a root of minpoly K (f a). -/
theorem minpoly_eq_iff_isRoot (f : A →ₐ[K] B) (a : A)
    (ha : IsIntegral K a) (hfa : IsIntegral K (f a)) :
    minpoly K (f a) = minpoly K a ↔ (minpoly K (f a)).IsRoot a := by
  simp only [Polynomial.IsRoot, ← Polynomial.aeval_def]
  exact minpoly_eq_iff_aeval_zero f a ha hfa

/-- **Failure mode**: minpoly K (f a) ≠ minpoly K a iff a is NOT a root of minpoly K (f a).
    This means f has "collapsed" an algebraic relation that a satisfies. -/
theorem minpoly_ne_iff_not_aeval_zero (f : A →ₐ[K] B) (a : A)
    (ha : IsIntegral K a) (hfa : IsIntegral K (f a)) :
    minpoly K (f a) ≠ minpoly K a ↔
    Polynomial.aeval a (minpoly K (f a)) ≠ 0 :=
  (minpoly_eq_iff_aeval_zero f a ha hfa).ne

-- ============================================================================
-- Part III: Connection to the Injective Case
-- ============================================================================

/-- The injective case: `minpoly.algHom_eq` is a special case of our characterization.
    When f is injective, the characterization is trivially satisfied. -/
theorem injective_implies_criterion_holds (f : A →ₐ[K] B) (hf : Function.Injective f)
    (a : A) (ha : IsIntegral K a) :
    Polynomial.aeval a (minpoly K (f a)) = 0 := by
  rw [minpoly.algHom_eq f hf a]
  exact minpoly.aeval K a

/-- The injective case follows from the characterization. -/
theorem injective_iff_implies_criterion_always (f : A →ₐ[K] B)
    (a : A) (ha : IsIntegral K a) (hfa : IsIntegral K (f a)) :
    (Function.Injective f → minpoly K (f a) = minpoly K a) ↔
    (Function.Injective f → Polynomial.aeval a (minpoly K (f a)) = 0) := by
  constructor
  · intro hfn hf
    rw [hfn hf]; exact minpoly.aeval K a
  · intro hcrit hf
    rw [minpoly_eq_iff_aeval_zero f a ha hfa]
    exact hcrit hf

-- ============================================================================
-- Part IV: Degree Consequence
-- ============================================================================

/-- **Degree inequality**: natDegree(minpoly K (f a)) ≤ natDegree(minpoly K a).
    Non-injective maps can only DECREASE the minimal polynomial degree. -/
theorem minpoly_natDegree_le (f : A →ₐ[K] B) (a : A) (ha : IsIntegral K a) :
    (minpoly K (f a)).natDegree ≤ (minpoly K a).natDegree := by
  rcases eq_or_ne (minpoly K (f a)) 0 with h | h
  · simp [h]
  · exact natDegree_le_of_dvd (minpoly_dvd_algHom f a) (minpoly.ne_zero ha)

/-- The characterization implies degree equality when minpolies are equal. -/
theorem minpoly_eq_implies_degree_eq (f : A →ₐ[K] B) (a : A)
    (ha : IsIntegral K a) (hfa : IsIntegral K (f a)) :
    minpoly K (f a) = minpoly K a →
    (minpoly K (f a)).natDegree = (minpoly K a).natDegree := by
  intro h; rw [h]

-- ============================================================================
-- Part V: The Complete Picture
-- ============================================================================

/-- **Summary** of the characterization:

    For any K-algebra map f : A →ₐ[K] B and integral element a : A:

    1. ALWAYS: minpoly(f a) ∣ minpoly(a)  [minpoly_dvd_algHom]
    2. ALWAYS: deg(minpoly(f a)) ≤ deg(minpoly(a))  [minpoly_natDegree_le]
    3. EQUALITY: minpoly(f a) = minpoly(a) ↔ aeval a (minpoly(f a)) = 0

    The injective case `minpoly.algHom_eq` (from OQ02OQ01) follows because:
    - For injective f: aeval (f a) (minpoly a) = 0 (by aeval_algHom)
    - Since f is injective: f⁻¹(0) = {0}, so aeval a (minpoly(f a)) = 0

    For NON-INJECTIVE f: the characterization gives a testable criterion —
    just check whether aeval a (minpoly K (f a)) = 0. This can fail:
    - Example: zero map f ≡ 0. Then f(a) = 0 for all a, minpoly K (0) = X.
      aeval a X = a. So the criterion fails iff a ≠ 0 (as expected). -/
theorem complete_characterization (f : A →ₐ[K] B) (a : A)
    (ha : IsIntegral K a) (hfa : IsIntegral K (f a)) :
    minpoly K (f a) = minpoly K a ↔
    Polynomial.aeval a (minpoly K (f a)) = 0 :=
  minpoly_eq_iff_aeval_zero f a ha hfa

end MinpolyNonInjectiveChar
