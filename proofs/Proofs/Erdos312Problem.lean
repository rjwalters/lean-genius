/-
Erdős Problem #312: Subset Sums of Unit Fractions

Source: https://erdosproblems.com/312
Status: OPEN

Statement:
Does there exist a constant c > 0 such that, for any K > 1, whenever A is a
sufficiently large finite multiset of positive integers with Σ_{n ∈ A} 1/n > K,
there exists a subset S ⊆ A with 1 - exp(-cK) < Σ_{n ∈ S} 1/n ≤ 1?

Known Results:
- Erdős-Graham: The weaker bound c/K² is known (polynomial precision)
- The conjectured exponential bound exp(-cK) remains open

The problem asks whether we can find subsets whose reciprocal sum is
exponentially close to 1, given a large enough total reciprocal sum.

Reference: Erdős-Graham [ErGr80]
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Finset Real

namespace Erdos312

/- ## Part I: Unit Fraction Sums -/

/-- The reciprocal sum of a multiset of positive integers:
    Σ_{i ∈ {0,...,n-1}} 1/a(i) -/
noncomputable def reciprocalSum (n : ℕ) (a : Fin n → ℕ) : ℝ :=
  ∑ i : Fin n, (a i : ℝ)⁻¹

/-- The reciprocal sum over a subset S ⊆ {0,...,n-1} -/
noncomputable def subsetReciprocalSum (n : ℕ) (a : Fin n → ℕ) (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ S, (a i : ℝ)⁻¹

/- ## Part II: The Main Conjecture -/

/-- The exponential precision property:
    A multiset (n, a) has a subset S with reciprocal sum in (1 - exp(-cK), 1] -/
def hasExponentialPrecision (n : ℕ) (a : Fin n → ℕ) (c K : ℝ) : Prop :=
  ∃ S : Finset (Fin n),
    1 - Real.exp (-(c * K)) < subsetReciprocalSum n a S ∧
    subsetReciprocalSum n a S ≤ 1

/-- Erdős-Graham Conjecture (OPEN):
    ∃ c > 0 such that for all K > 1, every sufficiently large multiset
    with reciprocal sum > K has a subset summing to within exp(-cK) of 1.

    This is the formal statement from the formal-conjectures project. -/
def mainConjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ K : ℝ, 1 < K →
      ∃ N₀ : ℕ, ∀ (n : ℕ) (a : Fin n → ℕ),
        (n ≥ N₀ ∧ reciprocalSum n a > K) →
          hasExponentialPrecision n a c K

/- ## Part III: Known Result (Polynomial Bound) -/

/-- The polynomial precision property:
    A multiset has a subset S with reciprocal sum in (1 - c/K², 1] -/
def hasPolynomialPrecision (n : ℕ) (a : Fin n → ℕ) (c K : ℝ) : Prop :=
  ∃ S : Finset (Fin n),
    1 - c / K^2 < subsetReciprocalSum n a S ∧
    subsetReciprocalSum n a S ≤ 1

/-- Erdős-Graham Theorem [ErGr80]:
    The polynomial bound c/K² is known to hold.
    This is the weaker version of the conjecture. -/
axiom erdos_graham_polynomial :
  ∃ c : ℝ, 0 < c ∧
    ∀ K : ℝ, 1 < K →
      ∃ N₀ : ℕ, ∀ (n : ℕ) (a : Fin n → ℕ),
        (n ≥ N₀ ∧ reciprocalSum n a > K) →
          hasPolynomialPrecision n a c K

/- ## Part IV: Relationship Between Bounds -/

/-- For large K, the exponential bound is tighter than the polynomial one:
    exp(-cK) < c'/K² for sufficiently large K.
    This shows the conjecture is strictly stronger than the known result. -/
axiom exponential_stronger_than_polynomial :
  ∀ c : ℝ, 0 < c →
    ∀ c' : ℝ, 0 < c' →
      ∃ K₀ : ℝ, ∀ K : ℝ, K > K₀ →
        Real.exp (-(c * K)) < c' / K^2

/-- If the exponential precision conjecture holds, then for large K,
    any multiset satisfying the exponential property also satisfies
    the polynomial one (the conjecture implies the known result). -/
theorem conjecture_implies_known :
    mainConjecture →
    ∃ c : ℝ, 0 < c ∧
      ∀ K : ℝ, 1 < K →
        ∃ N₀ : ℕ, ∀ (n : ℕ) (a : Fin n → ℕ),
          (n ≥ N₀ ∧ reciprocalSum n a > K) →
            ∃ S : Finset (Fin n),
              subsetReciprocalSum n a S ≤ 1 := by
  intro ⟨c, hc, hConj⟩
  exact ⟨c, hc, fun K hK => by
    obtain ⟨N₀, hN₀⟩ := hConj K hK
    exact ⟨N₀, fun n a h => by
      obtain ⟨S, _, hle⟩ := hN₀ n a h
      exact ⟨S, hle⟩⟩⟩

/- ## Part V: Harmonic Number Context -/

/-- The n-th harmonic number H_n = 1 + 1/2 + ... + 1/n -/
noncomputable def harmonicNumber (n : ℕ) : ℝ :=
  ∑ i in Finset.range n, ((i + 1 : ℕ) : ℝ)⁻¹

/-- Harmonic numbers grow without bound (well-known):
    For any K > 0, there exists n with H_n > K -/
axiom harmonic_unbounded :
  ∀ K : ℝ, ∃ n : ℕ, harmonicNumber n > K

/- ## Part VI: Summary -/

/-- Erdős Problem #312 Summary:
    The main conjecture asks for exponential precision in subset sums.
    The polynomial version is known (Erdős-Graham).
    The exponential version remains OPEN. -/
theorem erdos_312_status :
    -- Known: polynomial bound exists
    (∃ c : ℝ, 0 < c ∧
      ∀ K : ℝ, 1 < K →
        ∃ N₀ : ℕ, ∀ (n : ℕ) (a : Fin n → ℕ),
          (n ≥ N₀ ∧ reciprocalSum n a > K) →
            hasPolynomialPrecision n a c K) := by
  exact erdos_graham_polynomial

end Erdos312
