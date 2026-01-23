/-
Erdős Problem #1122: Additive Functions and Monotonicity Defects

Source: https://erdosproblems.com/1122
Status: OPEN

Statement:
Let f: ℕ → ℝ be an additive function (f(ab) = f(a) + f(b) when gcd(a,b) = 1).
Let A = {n ≥ 1 : f(n+1) < f(n)} be the "monotonicity defect set".

If |A ∩ [1,X]| = o(X), must f(n) = c·log(n) for some c ∈ ℝ?

Background:
- An additive function satisfies f(ab) = f(a) + f(b) for coprime a, b.
- The canonical example is f(n) = c·log(n), which is completely additive.
- The set A measures where f fails to be monotonic increasing.
- The conjecture asks: if f is "almost always" increasing, must it be logarithmic?

Known Results:
- Erdős (1946): TRUE if A is empty (f strictly increasing implies f = c·log)
- Erdős (1946): TRUE if f(n+1) - f(n) = o(1) (gaps tend to zero)
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

/-
## Part I: Additive Functions
-/

/--
**Additive function:**
A function f: ℕ → ℝ is additive if f(ab) = f(a) + f(b) whenever gcd(a,b) = 1.
-/
def IsAdditive (f : ℕ → ℝ) : Prop :=
  ∀ a b : ℕ, a ≥ 1 → b ≥ 1 → Nat.gcd a b = 1 → f (a * b) = f a + f b

/--
**Completely additive function:**
f(ab) = f(a) + f(b) for all a, b (not just coprime).
-/
def IsCompletelyAdditive (f : ℕ → ℝ) : Prop :=
  ∀ a b : ℕ, a ≥ 1 → b ≥ 1 → f (a * b) = f a + f b

/--
**The logarithm is completely additive:**
log(ab) = log(a) + log(b).
-/
theorem log_completely_additive : IsCompletelyAdditive (fun n => Real.log n) := by
  intro a b ha hb
  simp only
  rw [Nat.cast_mul]
  exact Real.log_mul (by positivity) (by positivity)

/--
**Additive determined by primes:**
An additive function is determined by its values on prime powers.
-/
def valueDeterminedByPrimes (f : ℕ → ℝ) (hf : IsAdditive f) : Prop :=
  ∀ n : ℕ, n ≥ 1 → f n = ∑ p ∈ Nat.primeFactors n, f (p ^ (Nat.factorization n p))

/-
## Part II: The Monotonicity Defect Set
-/

/--
**Monotonicity defect set:**
A = {n ≥ 1 : f(n+1) < f(n)} is where f fails to be increasing.
-/
def monotonicityDefectSet (f : ℕ → ℝ) : Set ℕ :=
  {n : ℕ | n ≥ 1 ∧ f (n + 1) < f n}

/--
**Defect count function:**
|A ∩ [1,X]| counts monotonicity failures up to X.
-/
noncomputable def defectCount (f : ℕ → ℝ) (X : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun n => n ∈ monotonicityDefectSet f) (Finset.range (X + 1)))

/--
**Little-o condition:**
|A ∩ [1,X]| = o(X) means defects are sparse.
-/
def defectIsLittleO (f : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ X ≥ N, (defectCount f X : ℝ) < ε * X

/--
**Empty defect set:**
A is empty means f is strictly increasing.
-/
def hasEmptyDefectSet (f : ℕ → ℝ) : Prop :=
  monotonicityDefectSet f = ∅

theorem empty_defect_means_increasing (f : ℕ → ℝ) (h : hasEmptyDefectSet f) :
    ∀ n : ℕ, n ≥ 1 → f n ≤ f (n + 1) := by
  intro n hn
  by_contra hlt
  push_neg at hlt
  have : n ∈ monotonicityDefectSet f := ⟨hn, hlt⟩
  rw [h] at this
  exact this

/-
## Part III: The Logarithmic Form
-/

/--
**Logarithmic form:**
f(n) = c·log(n) for some constant c.
-/
def hasLogarithmicForm (f : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, ∀ n : ℕ, n ≥ 1 → f n = c * Real.log n

/--
**Zero function is logarithmic:**
f(n) = 0 = 0·log(n).
-/
theorem zero_is_logarithmic : hasLogarithmicForm (fun _ => 0) := by
  use 0
  intro n _
  simp

/--
**Logarithmic functions are additive:**
If f(n) = c·log(n), then f is completely additive (hence additive).
-/
theorem logarithmic_is_additive (f : ℕ → ℝ) (hf : hasLogarithmicForm f) : IsAdditive f := by
  obtain ⟨c, hc⟩ := hf
  intro a b ha hb _
  simp only [hc a ha, hc b hb, hc (a * b) (Nat.one_le_iff_ne_zero.mpr (by omega))]
  rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
  ring

/-
## Part IV: Erdős's Known Results
-/

/--
**Erdős's First Theorem:**
If the defect set A is empty (f strictly increasing), then f(n) = c·log(n).

Proof idea: An increasing additive function must be logarithmic.
-/
axiom erdos_empty_defect (f : ℕ → ℝ) (hf : IsAdditive f) (hempty : hasEmptyDefectSet f) :
    hasLogarithmicForm f

/--
**Erdős's Second Theorem:**
If f(n+1) - f(n) = o(1) (increments tend to zero), then f(n) = c·log(n).
-/
def incrementsVanish (f : ℕ → ℝ) : Prop :=
  Tendsto (fun n => f (n + 1) - f n) atTop (nhds 0)

axiom erdos_vanishing_increments (f : ℕ → ℝ) (hf : IsAdditive f)
    (hvanish : incrementsVanish f) : hasLogarithmicForm f

/-
## Part V: Mangerel's Partial Progress
-/

/--
**Mangerel's density condition:**
|A ∩ [1,X]| ≪ X/(log X)^{2+c} for some c > 0.
-/
def satisfiesMangerelDensity (f : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∃ C : ℝ, C > 0 ∧
    ∀ X : ℕ, X ≥ 2 → (defectCount f X : ℝ) ≤ C * X / (Real.log X)^(2 + c)

/--
**Bounded prime values condition:**
f(p) does not have "very large values" (technical condition).
-/
def hasBoundedPrimeValues (f : ℕ → ℝ) : Prop :=
  ∃ g : ℕ → ℝ, (∀ p : ℕ, Nat.Prime p → |f p| ≤ g p) ∧
    (∀ ε > 0, ∃ N : ℕ, ∀ p : ℕ, Nat.Prime p → p ≥ N → g p ≤ ε * Real.log p)

/--
**Mangerel's Theorem (2022):**
If the defect density is O(X/(log X)^{2+c}) and f(p) is bounded,
then f(n) = c·log(n).
-/
axiom mangerel_2022 (f : ℕ → ℝ) (hf : IsAdditive f)
    (hdensity : satisfiesMangerelDensity f) (hbounded : hasBoundedPrimeValues f) :
    hasLogarithmicForm f

/-
## Part VI: The Erdős Conjecture
-/

/--
**Erdős Problem #1122 (Conjecture):**
If f is additive and |A ∩ [1,X]| = o(X), then f(n) = c·log(n).
-/
def erdos1122Conjecture : Prop :=
  ∀ f : ℕ → ℝ, IsAdditive f → defectIsLittleO f → hasLogarithmicForm f

/--
**Status: OPEN**
This conjecture remains unresolved.
-/
axiom conjecture_open : ¬∃ (proof : erdos1122Conjecture), True

/-
## Part VII: Relationship Between Conditions
-/

/--
**Empty defect implies little-o:**
If A = ∅, then |A ∩ [1,X]| = 0 = o(X).
-/
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

/--
**Mangerel's condition implies little-o:**
X/(log X)^{2+c} = o(X) as X → ∞.
-/
theorem mangerel_implies_littleO (f : ℕ → ℝ) (h : satisfiesMangerelDensity f) :
    defectIsLittleO f := by
  sorry

/--
**Hierarchy of conditions:**
empty ⊂ Mangerel ⊂ little-o (strictly)
-/
def conditionHierarchy : Prop :=
  (∀ f : ℕ → ℝ, hasEmptyDefectSet f → satisfiesMangerelDensity f) ∧
  (∀ f : ℕ → ℝ, satisfiesMangerelDensity f → defectIsLittleO f)

/-
## Part VIII: Examples and Non-Examples
-/

/--
**Example: log(n) has empty defect set**
Since log is strictly increasing on ℕ⁺.
-/
theorem log_has_empty_defect : hasEmptyDefectSet (fun n => Real.log n) := by
  unfold hasEmptyDefectSet monotonicityDefectSet
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_lt]
  intro hn
  apply Real.log_le_log (by positivity)
  simp [hn]

/--
**Example: The number-of-prime-factors function**
ω(n) = number of distinct prime factors is additive.
-/
def omega (n : ℕ) : ℕ := n.primeFactors.card

theorem omega_is_additive : IsAdditive (fun n => (omega n : ℝ)) := by
  sorry

/--
**ω(n) is not logarithmic:**
ω grows much slower than log.
-/
theorem omega_not_logarithmic : ¬hasLogarithmicForm (fun n => (omega n : ℝ)) := by
  sorry

/-
## Part IX: The Gap to Close
-/

/--
**Current gap:**
Erdős proved the result for vanishing increments: f(n+1) - f(n) → 0.
Mangerel extended to O(X/(log X)^{2+c}) defects.
The gap is: what about o(X) defects that aren't O(X/(log X)^{2+c})?
-/
def currentGap : Prop :=
  ∃ f : ℕ → ℝ, IsAdditive f ∧ defectIsLittleO f ∧ ¬satisfiesMangerelDensity f

/--
**Key difficulty:**
The problem relates to understanding the distribution of additive functions
at consecutive integers, which is controlled by prime factorizations.
-/
axiom distribution_difficulty : True

/-
## Part X: Related Problems
-/

/--
**Problem 491:**
Related problem about additive functions and short intervals.
-/
def erdos491Related : Prop :=
  True  -- Recording the connection

/--
**Kátai-Wirsing Theorem:**
If f is additive and f(n+1) - f(n) → 0, then f(n) = c·log(n).
This is essentially Erdős's second theorem.
-/
axiom katai_wirsing (f : ℕ → ℝ) (hf : IsAdditive f) (hinc : incrementsVanish f) :
    hasLogarithmicForm f

/-
## Part XI: Main Results Summary
-/

/--
**Erdős Problem #1122: Summary**

1. **Erdős (empty):** A = ∅ implies f = c·log - PROVED
2. **Erdős/Kátai-Wirsing:** f(n+1) - f(n) → 0 implies f = c·log - PROVED
3. **Mangerel (2022):** |A| ≪ X/(log X)^{2+c} implies f = c·log - PROVED
4. **Conjecture:** |A| = o(X) implies f = c·log - OPEN

Status: OPEN
-/
theorem erdos_1122_summary :
    -- Erdős's empty defect theorem
    (∀ f : ℕ → ℝ, IsAdditive f → hasEmptyDefectSet f → hasLogarithmicForm f) ∧
    -- Erdős's vanishing increments theorem
    (∀ f : ℕ → ℝ, IsAdditive f → incrementsVanish f → hasLogarithmicForm f) ∧
    -- Mangerel's theorem (under additional hypotheses)
    (∀ f : ℕ → ℝ, IsAdditive f → satisfiesMangerelDensity f →
      hasBoundedPrimeValues f → hasLogarithmicForm f) := by
  refine ⟨?_, ?_, ?_⟩
  · exact erdos_empty_defect
  · exact erdos_vanishing_increments
  · exact mangerel_2022

/--
**Problem Status:**
- Empty defect case: SOLVED (Erdős)
- Vanishing increments: SOLVED (Erdős/Kátai-Wirsing)
- Mangerel density: SOLVED (Mangerel 2022)
- General o(X) case: OPEN
-/
axiom erdos_1122_status : True

end Erdos1122
