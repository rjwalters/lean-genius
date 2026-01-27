/-
Erdős Problem #1122: Additive Functions and Monotonicity Defects

Source: https://erdosproblems.com/1122
Status: OPEN
Reference: Erdős [Er46], Mangerel [Ma22]

Statement:
Let f: ℕ → ℝ be an additive function (f(ab) = f(a) + f(b) when gcd(a,b) = 1).
Let A = {n ≥ 1 : f(n+1) < f(n)} be the "monotonicity defect set".

If |A ∩ [1,X]| = o(X), must f(n) = c·log(n) for some c ∈ ℝ?

Known Results:
- Erdős (1946): TRUE if A is empty (f strictly increasing implies f = c·log)
- Erdős (1946): TRUE if f(n+1) - f(n) = o(1) (Kátai-Wirsing theorem)
- Mangerel (2022): TRUE if |A ∩ [1,X]| ≪ X/(log X)^{2+c} and f(p) bounded

References:
- Erdős, P. (1946): On the distribution function of additive functions
- Mangerel, A.P. (2022): Additive functions in short intervals, gaps and a
  conjecture of Erdős. Ramanujan J., 1023-1090.
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic

open Nat Real Filter

namespace Erdos1122

/-!
# Erdős Problem 1122: Additive Functions and Monotonicity Defects

*Reference:* [erdosproblems.com/1122](https://www.erdosproblems.com/1122)

An additive function f: ℕ → ℝ satisfies f(ab) = f(a) + f(b) when gcd(a,b) = 1.
The conjecture asks whether sparse monotonicity defects force f to be logarithmic.
-/

/-! ## Additive Functions -/

/-- An additive function satisfies f(ab) = f(a) + f(b) when gcd(a,b) = 1. -/
def IsAdditive (f : ℕ → ℝ) : Prop :=
  ∀ a b : ℕ, a ≥ 1 → b ≥ 1 → Nat.gcd a b = 1 → f (a * b) = f a + f b

/-- A completely additive function satisfies f(ab) = f(a) + f(b) for all a, b. -/
def IsCompletelyAdditive (f : ℕ → ℝ) : Prop :=
  ∀ a b : ℕ, a ≥ 1 → b ≥ 1 → f (a * b) = f a + f b

/-- The logarithm is completely additive: log(ab) = log(a) + log(b). -/
theorem log_completely_additive : IsCompletelyAdditive (fun n => Real.log n) := by
  intro a b ha hb
  simp only
  rw [Nat.cast_mul]
  exact Real.log_mul (by positivity) (by positivity)

/-- An additive function is determined by its values on prime powers. -/
def valueDeterminedByPrimes (f : ℕ → ℝ) (hf : IsAdditive f) : Prop :=
  ∀ n : ℕ, n ≥ 1 → f n = ∑ p ∈ Nat.primeFactors n, f (p ^ (Nat.factorization n p))

/-! ## The Monotonicity Defect Set -/

/-- A = {n ≥ 1 : f(n+1) < f(n)} is the set where f fails to be increasing. -/
def monotonicityDefectSet (f : ℕ → ℝ) : Set ℕ :=
  {n : ℕ | n ≥ 1 ∧ f (n + 1) < f n}

/-- |A ∩ [1,X]| counts monotonicity failures up to X. -/
noncomputable def defectCount (f : ℕ → ℝ) (X : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun n => n ∈ monotonicityDefectSet f) (Finset.range (X + 1)))

/-- |A ∩ [1,X]| = o(X) means defects are asymptotically sparse. -/
def defectIsLittleO (f : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ X ≥ N, (defectCount f X : ℝ) < ε * X

/-- A is empty means f is (weakly) increasing. -/
def hasEmptyDefectSet (f : ℕ → ℝ) : Prop :=
  monotonicityDefectSet f = ∅

/-- If A = ∅, then f(n) ≤ f(n+1) for all n ≥ 1. -/
theorem empty_defect_means_increasing (f : ℕ → ℝ) (h : hasEmptyDefectSet f) :
    ∀ n : ℕ, n ≥ 1 → f n ≤ f (n + 1) := by
  intro n hn
  by_contra hlt
  push_neg at hlt
  have : n ∈ monotonicityDefectSet f := ⟨hn, hlt⟩
  rw [h] at this
  exact this

/-! ## The Logarithmic Form -/

/-- f(n) = c·log(n) for some constant c. -/
def hasLogarithmicForm (f : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, ∀ n : ℕ, n ≥ 1 → f n = c * Real.log n

/-- The zero function is logarithmic (c = 0). -/
theorem zero_is_logarithmic : hasLogarithmicForm (fun _ => 0) := by
  use 0
  intro n _
  simp

/-- Logarithmic functions are additive. -/
theorem logarithmic_is_additive (f : ℕ → ℝ) (hf : hasLogarithmicForm f) : IsAdditive f := by
  obtain ⟨c, hc⟩ := hf
  intro a b ha hb _
  simp only [hc a ha, hc b hb, hc (a * b) (Nat.one_le_iff_ne_zero.mpr (by omega))]
  rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
  ring

/-! ## Erdős's Known Results -/

/-- Erdős (1946): If A = ∅ (f strictly increasing), then f = c·log.
    An increasing additive function must be logarithmic. -/
axiom erdos_empty_defect (f : ℕ → ℝ) (hf : IsAdditive f) (hempty : hasEmptyDefectSet f) :
    hasLogarithmicForm f

/-- Increments vanish: f(n+1) - f(n) → 0 as n → ∞. -/
def incrementsVanish (f : ℕ → ℝ) : Prop :=
  Tendsto (fun n => f (n + 1) - f n) atTop (nhds 0)

/-- Erdős (1946) / Kátai-Wirsing: If f(n+1) - f(n) → 0, then f = c·log. -/
axiom erdos_vanishing_increments (f : ℕ → ℝ) (hf : IsAdditive f)
    (hvanish : incrementsVanish f) : hasLogarithmicForm f

/-! ## Mangerel's Partial Progress (2022) -/

/-- Mangerel's density condition: |A ∩ [1,X]| ≪ X/(log X)^{2+c} for some c > 0. -/
def satisfiesMangerelDensity (f : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∃ C : ℝ, C > 0 ∧
    ∀ X : ℕ, X ≥ 2 → (defectCount f X : ℝ) ≤ C * X / (Real.log X)^(2 + c)

/-- Bounded prime values: f(p) does not grow too fast relative to log(p). -/
def hasBoundedPrimeValues (f : ℕ → ℝ) : Prop :=
  ∃ g : ℕ → ℝ, (∀ p : ℕ, Nat.Prime p → |f p| ≤ g p) ∧
    (∀ ε > 0, ∃ N : ℕ, ∀ p : ℕ, Nat.Prime p → p ≥ N → g p ≤ ε * Real.log p)

/-- Mangerel (2022): Under density bound and bounded prime values, f = c·log.
    Reference: Ramanujan J. (2022), 1023-1090. -/
axiom mangerel_2022 (f : ℕ → ℝ) (hf : IsAdditive f)
    (hdensity : satisfiesMangerelDensity f) (hbounded : hasBoundedPrimeValues f) :
    hasLogarithmicForm f

/-! ## The Erdős Conjecture -/

/-- Erdős Problem #1122 (OPEN):
    If f is additive and |A ∩ [1,X]| = o(X), then f(n) = c·log(n). -/
def erdos1122Conjecture : Prop :=
  ∀ f : ℕ → ℝ, IsAdditive f → defectIsLittleO f → hasLogarithmicForm f

/-- The conjecture is axiomatized as the problem is OPEN. -/
axiom erdos_1122 : erdos1122Conjecture

/-! ## Condition Hierarchy -/

/-- If A = ∅, then |A ∩ [1,X]| = 0 = o(X). -/
theorem empty_implies_littleO (f : ℕ → ℝ) (h : hasEmptyDefectSet f) : defectIsLittleO f := by
  intro ε hε
  use 1
  intro X _
  have : defectCount f X = 0 := by
    unfold defectCount
    simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro n _
    rw [h]
    exact Set.not_mem_empty n
  simp [this, hε]

/-- Mangerel's condition implies o(X): X/(log X)^{2+c} = o(X) as X → ∞. -/
axiom mangerel_implies_littleO (f : ℕ → ℝ) (h : satisfiesMangerelDensity f) :
    defectIsLittleO f

/-- The hierarchy of conditions:
    empty defect ⊂ Mangerel density ⊂ o(X) density (each strictly weaker). -/
def conditionHierarchy : Prop :=
  (∀ f : ℕ → ℝ, hasEmptyDefectSet f → satisfiesMangerelDensity f) ∧
  (∀ f : ℕ → ℝ, satisfiesMangerelDensity f → defectIsLittleO f)

/-! ## Examples -/

/-- log(n) has empty defect set: log is strictly increasing on ℕ⁺. -/
theorem log_has_empty_defect : hasEmptyDefectSet (fun n => Real.log n) := by
  unfold hasEmptyDefectSet monotonicityDefectSet
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_lt]
  intro hn
  apply Real.log_le_log (by positivity)
  simp [hn]

/-- ω(n) = number of distinct prime factors is additive (but not logarithmic). -/
def omega (n : ℕ) : ℕ := n.primeFactors.card

/-- ω is additive: ω(ab) = ω(a) + ω(b) for coprime a, b. -/
axiom omega_is_additive : IsAdditive (fun n => (omega n : ℝ))

/-- ω is not logarithmic: it grows much slower than log. -/
axiom omega_not_logarithmic : ¬hasLogarithmicForm (fun n => (omega n : ℝ))

/-! ## Summary of Known Results -/

/-- Consolidation of the three known positive results:
    1. Empty defect → logarithmic (Erdős 1946)
    2. Vanishing increments → logarithmic (Erdős/Kátai-Wirsing)
    3. Mangerel density + bounded primes → logarithmic (Mangerel 2022) -/
theorem erdos_1122_summary :
    (∀ f : ℕ → ℝ, IsAdditive f → hasEmptyDefectSet f → hasLogarithmicForm f) ∧
    (∀ f : ℕ → ℝ, IsAdditive f → incrementsVanish f → hasLogarithmicForm f) ∧
    (∀ f : ℕ → ℝ, IsAdditive f → satisfiesMangerelDensity f →
      hasBoundedPrimeValues f → hasLogarithmicForm f) := by
  refine ⟨?_, ?_, ?_⟩
  · exact erdos_empty_defect
  · exact erdos_vanishing_increments
  · exact mangerel_2022

end Erdos1122
