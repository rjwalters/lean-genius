import Mathlib

/-
# OQ-05: Minimal Polynomial Reduction in General K-Algebras

Extends the minimal polynomial reduction theory from matrices to arbitrary
K-algebras. For any integral element x in a K-algebra A, we prove:

1. **Reduction**: aeval x f = aeval x (f mod minpoly K x)
2. **Annihilator**: aeval x f = 0 ↔ minpoly K x | f
3. **Congruence**: aeval x f = aeval x g ↔ minpoly K x | (f - g)
4. **Power reduction**: Higher powers reduce via minpoly
5. **Degree bound**: Remainders have degree < deg(minpoly)

All results use Mathlib's general minpoly infrastructure, which works for
any integral element in a K-algebra (not just matrices).
-/

set_option linter.unusedVariables false

namespace MinpolyReductionAlg

open Polynomial

variable {K : Type*} [Field K]
variable {A : Type*} [Ring A] [Algebra K A]

-- ============================================================
-- SECTION I: Core Reduction Theorem
-- ============================================================

-- The minimal polynomial reduction: evaluating f at x equals evaluating
-- the remainder of f modulo the minimal polynomial.
theorem minpoly_reduction (x : A) (hx : IsIntegral K x) (f : K[X]) :
    aeval x f = aeval x (f %ₘ minpoly K x) := by
  have hmonic : (minpoly K x).Monic := minpoly.monic hx
  -- f = (f /ₘ minpoly) * minpoly + (f %ₘ minpoly)
  have hdiv := modByMonic_add_div f hmonic
  -- Evaluate both sides at x
  calc aeval x f
      = aeval x ((f %ₘ minpoly K x) + (minpoly K x) * (f /ₘ minpoly K x)) := by
        rw [hdiv]
    _ = aeval x (f %ₘ minpoly K x) + aeval x ((minpoly K x) * (f /ₘ minpoly K x)) := by
        rw [map_add]
    _ = aeval x (f %ₘ minpoly K x) + aeval x (minpoly K x) * aeval x (f /ₘ minpoly K x) := by
        rw [map_mul]
    _ = aeval x (f %ₘ minpoly K x) + 0 * aeval x (f /ₘ minpoly K x) := by
        rw [minpoly.aeval]
    _ = aeval x (f %ₘ minpoly K x) := by simp

-- The quotient part vanishes under evaluation
theorem minpoly_quotient_vanishes (x : A) (hx : IsIntegral K x) (f : K[X]) :
    aeval x (minpoly K x * (f /ₘ minpoly K x)) = 0 := by
  rw [map_mul, minpoly.aeval, zero_mul]

-- The difference f - (f mod minpoly) is annihilated by x
theorem minpoly_reduction_diff (x : A) (hx : IsIntegral K x) (f : K[X]) :
    aeval x (f - f %ₘ minpoly K x) = 0 := by
  rw [map_sub, minpoly_reduction x hx f, sub_self]

-- ============================================================
-- SECTION II: Annihilator Characterization
-- ============================================================

-- Forward direction: if f annihilates x, then minpoly divides f
theorem minpoly_dvd_of_aeval_eq_zero (x : A) (hx : IsIntegral K x) (f : K[X])
    (hf : aeval x f = 0) : minpoly K x ∣ f :=
  minpoly.dvd K x hf

-- Backward direction: if minpoly divides f, then f annihilates x
theorem aeval_eq_zero_of_minpoly_dvd (x : A) (f : K[X])
    (hd : minpoly K x ∣ f) : aeval x f = 0 := by
  obtain ⟨g, hg⟩ := hd
  rw [hg, map_mul, minpoly.aeval, zero_mul]

-- The full characterization: annihilator ↔ divisibility
theorem minpoly_annihilator_iff (x : A) (hx : IsIntegral K x) (f : K[X]) :
    aeval x f = 0 ↔ minpoly K x ∣ f :=
  ⟨minpoly_dvd_of_aeval_eq_zero x hx f, aeval_eq_zero_of_minpoly_dvd x f⟩

-- The annihilator ideal is closed under addition
theorem annihilator_add (x : A) (hx : IsIntegral K x) (f g : K[X])
    (hf : aeval x f = 0) (hg : aeval x g = 0) : aeval x (f + g) = 0 := by
  rw [map_add, hf, hg, add_zero]

-- The annihilator ideal is closed under multiplication
theorem annihilator_mul_left (x : A) (f g : K[X])
    (hf : aeval x f = 0) : aeval x (f * g) = 0 := by
  rw [map_mul, hf, zero_mul]

-- ============================================================
-- SECTION III: Congruence and Quotient Structure
-- ============================================================

-- Congruence: same evaluation iff congruent modulo minpoly
theorem minpoly_congruence_iff (x : A) (hx : IsIntegral K x) (f g : K[X]) :
    aeval x f = aeval x g ↔ minpoly K x ∣ (f - g) := by
  rw [← sub_eq_zero, ← map_sub]
  exact minpoly_annihilator_iff x hx (f - g)

-- Same remainder implies same evaluation
theorem aeval_eq_of_modByMonic_eq (x : A) (hx : IsIntegral K x) (f g : K[X])
    (h : f %ₘ minpoly K x = g %ₘ minpoly K x) :
    aeval x f = aeval x g := by
  rw [minpoly_reduction x hx f, minpoly_reduction x hx g, h]

-- ============================================================
-- SECTION IV: Degree Bounds
-- ============================================================

-- The remainder has degree strictly less than the minimal polynomial
theorem reduction_degree_lt (x : A) (hx : IsIntegral K x) (f : K[X]) :
    (f %ₘ minpoly K x).natDegree < (minpoly K x).natDegree ∨
    f %ₘ minpoly K x = 0 := by
  by_cases h : f %ₘ minpoly K x = 0
  · right; exact h
  · left
    have hmonic := minpoly.monic hx
    have hlt := degree_modByMonic_lt f hmonic
    exact Polynomial.natDegree_lt_natDegree h hlt

-- The minimal polynomial has positive degree (it's irreducible, hence non-unit)
-- Requires the algebra to have no zero smul divisors (e.g., a domain)
theorem minpoly_natDegree_pos [Nontrivial A] [NoZeroSMulDivisors K A]
    (x : A) (hx : IsIntegral K x) :
    0 < (minpoly K x).natDegree :=
  minpoly.natDegree_pos hx

-- ============================================================
-- SECTION V: Power Reduction
-- ============================================================

-- Powers of x reduce via the minimal polynomial
theorem power_reduction (x : A) (hx : IsIntegral K x) (k : ℕ) :
    x ^ k = aeval x ((X ^ k : K[X]) %ₘ minpoly K x) := by
  rw [← minpoly_reduction x hx (X ^ k)]
  simp [aeval_X_pow]

-- x itself reduces to X mod minpoly (which is just X when deg > 1)
theorem element_reduction (x : A) (hx : IsIntegral K x) :
    x = aeval x ((X : K[X]) %ₘ minpoly K x) := by
  rw [← minpoly_reduction x hx X, aeval_X]

-- ============================================================
-- SECTION VI: Special Elements
-- ============================================================

-- Idempotent elements: x^2 = x implies minpoly divides X^2 - X
theorem minpoly_dvd_of_idempotent (x : A) (hx : IsIntegral K x)
    (hidem : x * x = x) : minpoly K x ∣ (X ^ 2 - X : K[X]) := by
  apply minpoly.dvd K x
  simp [sq, map_sub, aeval_X, hidem]

-- Involutory elements: x^2 = 1 implies minpoly divides X^2 - 1
theorem minpoly_dvd_of_involutory (x : A) (hx : IsIntegral K x)
    (hinv : x * x = 1) : minpoly K x ∣ (X ^ 2 - 1 : K[X]) := by
  apply minpoly.dvd K x
  simp [sq, map_sub, aeval_X, hinv, map_one]

-- Nilpotent elements: x^d = 0 implies minpoly divides X^d
theorem minpoly_dvd_of_nilpotent (x : A) (hx : IsIntegral K x)
    (d : ℕ) (hnil : x ^ d = 0) : minpoly K x ∣ (X ^ d : K[X]) := by
  apply minpoly.dvd K x
  simp [aeval_X_pow, hnil]

-- ============================================================
-- SECTION VII: Algebra Tower Reduction
-- ============================================================

-- In an algebra tower K → L → A, the minimal polynomial over L
-- divides the base change of the minimal polynomial over K.
-- This means the degree can only decrease when extending the base field.

section AlgebraTower

variable {L : Type*} [Field L] [Algebra K L] [Algebra L A] [IsScalarTower K L A]

-- Integrality transfers up the tower: integral over K implies integral over L
theorem isIntegral_tower_top (x : A) (hx : IsIntegral K x) : IsIntegral L x :=
  hx.tower_top

-- The base change of the K-minimal polynomial annihilates x over L.
-- Uses: eval₂ commutes with map, and algebraMap factors through the tower.
theorem minpoly_map_aeval_eq_zero (x : A) :
    aeval x ((minpoly K x).map (algebraMap K L)) = 0 := by
  rw [aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq K L A, ← aeval_def]
  exact minpoly.aeval K x

-- The base change preserves monicity
omit [Algebra L A] [IsScalarTower K L A] in
theorem minpoly_map_monic_tower (x : A) (hx : IsIntegral K x) :
    ((minpoly K x).map (algebraMap K L)).Monic :=
  (minpoly.monic hx).map (algebraMap K L)

-- Key theorem: minpoly over L divides the base-changed minpoly from K.
-- This is because the base-changed polynomial annihilates x and the minimal
-- polynomial divides any annihilating polynomial.
theorem minpoly_dvd_map_of_tower (x : A) (hx : IsIntegral K x) :
    minpoly L x ∣ (minpoly K x).map (algebraMap K L) :=
  minpoly.dvd L x (minpoly_map_aeval_eq_zero (L := L) x)

-- Degree consequence: the minimal polynomial degree can only decrease
-- when extending the base field from K to L.
theorem minpoly_natDegree_tower_le (x : A) (hx : IsIntegral K x) :
    (minpoly L x).natDegree ≤ (minpoly K x).natDegree := by
  have hdvd := minpoly_dvd_map_of_tower (L := L) x hx
  have hne : (minpoly K x).map (algebraMap K L) ≠ 0 :=
    (minpoly_map_monic_tower x hx).ne_zero
  have hmap_deg : ((minpoly K x).map (algebraMap K L)).natDegree =
      (minpoly K x).natDegree :=
    (minpoly.monic hx).natDegree_map (algebraMap K L)
  calc (minpoly L x).natDegree
      ≤ ((minpoly K x).map (algebraMap K L)).natDegree :=
        Polynomial.natDegree_le_of_dvd hdvd hne
    _ = (minpoly K x).natDegree := hmap_deg

-- Equality holds when the base-changed minpoly stays irreducible over L.
-- If p = map φ (minpoly K x) is irreducible over L, monic, and annihilates x,
-- then p must BE the minimal polynomial of x over L (by uniqueness).
theorem minpoly_eq_map_of_irreducible [IsDomain A] [NoZeroSMulDivisors L A]
    (x : A) (hx : IsIntegral K x)
    (hirr : Irreducible ((minpoly K x).map (algebraMap K L))) :
    minpoly L x = (minpoly K x).map (algebraMap K L) :=
  -- The base-changed polynomial is irreducible, monic, and annihilates x.
  -- By minimality of minpoly, it must equal the minimal polynomial over L.
  (minpoly.eq_of_irreducible_of_monic hirr
    (minpoly_map_aeval_eq_zero (L := L) x)
    (minpoly_map_monic_tower x hx)).symm

end AlgebraTower

end MinpolyReductionAlg
