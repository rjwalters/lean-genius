/-
Erdős Problem #288: Integer Harmonic Sums Over Interval Pairs

Source: https://erdosproblems.com/288
Status: OPEN

Statement:
Is it true that there are only finitely many pairs of intervals I₁, I₂
such that Σ_{n₁ ∈ I₁} 1/n₁ + Σ_{n₂ ∈ I₂} 1/n₂ ∈ ℕ?

Example: 1/3 + 1/4 + 1/5 + 1/6 + 1/20 = 1

This is still open even if |I₂| = 1. It is perhaps true with two
intervals replaced by any k intervals.

Reference: [ErGr80]
-/

import Mathlib.Data.Rat.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

open Finset BigOperators

namespace Erdos288

/- ## Part I: Harmonic Sums Over Intervals -/

/-- The harmonic sum over the interval [a, b] of positive integers:
    H(a, b) = Σ_{n=a}^{b} 1/n as a rational number. -/
noncomputable def harmonicInterval (a b : ℕ+) : ℚ :=
  ∑ n ∈ Finset.Icc (a : ℕ) (b : ℕ), if h : n > 0 then (n : ℚ)⁻¹ else 0

/-- An interval pair is represented by (a₁, b₁, a₂, b₂) where
    I₁ = [a₁, b₁] and I₂ = [a₂, b₂]. -/
def IntervalPair := ℕ+ × ℕ+ × ℕ+ × ℕ+

/-- The combined harmonic sum of an interval pair. -/
noncomputable def pairSum (p : IntervalPair) : ℚ :=
  harmonicInterval p.1 p.2.1 + harmonicInterval p.2.2.1 p.2.2.2

/-- The combined sum is a positive integer. -/
def IsIntegerSum (p : IntervalPair) : Prop :=
  ∃ n : ℕ+, pairSum p = (n : ℚ)

/- ## Part II: The Main Conjecture -/

/-- The set of interval pairs whose harmonic sum is a positive integer. -/
def integerSumPairs : Set IntervalPair :=
  {p | IsIntegerSum p}

/--
**Erdős Problem #288 (OPEN):**
There are only finitely many pairs of intervals (I₁, I₂) such that
the sum of their harmonic series is a positive integer.
-/
def ErdosConjecture288 : Prop :=
  Set.Finite integerSumPairs

/-- The conjecture is axiomatized. -/
axiom erdos_288 : ErdosConjecture288

/- ## Part III: The Known Examples -/

/-- Example: 1/3 + 1/4 + 1/5 + 1/6 + 1/20 = 1.
    This uses intervals [3,6] and [20,20]. -/
theorem example_sum_one :
    harmonicInterval ⟨3, by omega⟩ ⟨6, by omega⟩ +
    harmonicInterval ⟨20, by omega⟩ ⟨20, by omega⟩ = 1 := by
  unfold harmonicInterval
  -- Reduce the finite sums
  have h36 : Finset.Icc 3 6 = {3, 4, 5, 6} := by decide
  rw [h36, Finset.Icc_self]
  simp only [Finset.sum_singleton, Finset.sum_cons, Finset.sum_empty,
    show (3 : ℕ) > 0 from by omega, show (4 : ℕ) > 0 from by omega,
    show (5 : ℕ) > 0 from by omega, show (6 : ℕ) > 0 from by omega,
    show (20 : ℕ) > 0 from by omega, dif_pos, add_zero]
  norm_num

/-- Second example: 1/2 + 1/3 + 1/6 = 1.
    This uses intervals [2,3] and [6,6]. -/
theorem example_sum_one_v2 :
    harmonicInterval ⟨2, by omega⟩ ⟨3, by omega⟩ +
    harmonicInterval ⟨6, by omega⟩ ⟨6, by omega⟩ = 1 := by
  unfold harmonicInterval
  have h23 : Finset.Icc 2 3 = {2, 3} := by decide
  rw [h23, Finset.Icc_self]
  simp only [Finset.sum_singleton, Finset.sum_cons, Finset.sum_empty,
    show (2 : ℕ) > 0 from by omega, show (3 : ℕ) > 0 from by omega,
    show (6 : ℕ) > 0 from by omega, dif_pos, add_zero]
  norm_num

/-- Third example: 1/1 + 1/2 + 1/3 + 1/6 = 2.
    This uses intervals [1,3] and [6,6], showing the sum can be 2 (not just 1). -/
theorem example_sum_two :
    harmonicInterval ⟨1, by omega⟩ ⟨3, by omega⟩ +
    harmonicInterval ⟨6, by omega⟩ ⟨6, by omega⟩ = 2 := by
  unfold harmonicInterval
  have h13 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  rw [h13, Finset.Icc_self]
  simp only [Finset.sum_singleton, Finset.sum_cons, Finset.sum_empty,
    show (1 : ℕ) > 0 from by omega, show (2 : ℕ) > 0 from by omega,
    show (3 : ℕ) > 0 from by omega, show (6 : ℕ) > 0 from by omega,
    dif_pos, add_zero]
  norm_num

/- ## Part IV: Variant — Single Element I₂ -/

/-- The restricted version where I₂ has a single element. -/
def singletonPairs : Set (ℕ+ × ℕ+ × ℕ+) :=
  {p | ∃ n : ℕ+, harmonicInterval p.1 p.2.1 + (p.2.2 : ℚ)⁻¹ = (n : ℚ)}

-- **Variant (OPEN):**
-- The conjecture is still open even when |I₂| = 1.
-- Not axiomatized since it is not used by any theorem in this file.

/- ## Part V: Variant — k Intervals -/

/-- The generalization to k intervals: each interval represented
    as a pair (start, end) of positive naturals. -/
def kIntervalSum (k : ℕ) (I : Fin k → ℕ+ × ℕ+) : ℚ :=
  ∑ j : Fin k, harmonicInterval (I j).1 (I j).2

/-- The k-interval version of the conjecture. -/
def kIntervalPairs (k : ℕ) : Set (Fin k → ℕ+ × ℕ+) :=
  {I | ∃ n : ℕ+, kIntervalSum k I = (n : ℚ)}

-- **Extended Conjecture (OPEN):**
-- For any k, there are only finitely many k-tuples of intervals
-- whose harmonic sums add to a positive integer.
-- Not axiomatized since it is not used by any theorem in this file.

/- ## Part VI: Properties of Harmonic Sums -/

/-- The harmonic sum over [a, a] is 1/a. -/
theorem harmonicInterval_singleton (a : ℕ+) :
    harmonicInterval a a = (a : ℚ)⁻¹ := by
  unfold harmonicInterval
  rw [Finset.Icc_self]
  simp only [Finset.sum_singleton, dif_pos (PNat.pos a)]

/-- The harmonic sum is positive for valid intervals. -/
theorem harmonicInterval_pos (a b : ℕ+) (h : a ≤ b) :
    harmonicInterval a b > 0 := by
  unfold harmonicInterval
  apply Finset.sum_pos
  · -- Icc is nonempty since a ≤ b
    exact ⟨(a : ℕ), Finset.mem_Icc.mpr ⟨le_refl _, h⟩⟩
  · intro k hk
    have hk_pos : k > 0 := by
      have := (Finset.mem_Icc.mp hk).1; exact lt_of_lt_of_le (PNat.pos a) this
    simp only [dif_pos hk_pos]
    exact inv_pos.mpr (Nat.cast_pos.mpr hk_pos)

/-- The harmonic sum over [1, n] is the n-th harmonic number. -/
theorem harmonicInterval_from_one (n : ℕ+) :
    harmonicInterval 1 n = ∑ k ∈ Finset.Icc 1 (n : ℕ), (k : ℚ)⁻¹ := by
  unfold harmonicInterval
  apply Finset.sum_congr rfl
  intro k hk
  have hk_pos : k > 0 := by
    have := (Finset.mem_Icc.mp hk).1; omega
  simp only [dif_pos hk_pos]

/-- The harmonic sum H(a,b) is at least 1/a when a ≤ b.
    The single term at k = a gives this lower bound via Finset.single_le_sum. -/
theorem harmonicInterval_ge_inv_first (a b : ℕ+) (h : a ≤ b) :
    harmonicInterval a b ≥ (a : ℚ)⁻¹ := by
  unfold harmonicInterval
  have hmem : (a : ℕ) ∈ Finset.Icc (a : ℕ) (b : ℕ) :=
    Finset.mem_Icc.mpr ⟨le_refl _, h⟩
  have hnn : ∀ k ∈ Finset.Icc (a : ℕ) (b : ℕ),
      0 ≤ (if h : k > 0 then (k : ℚ)⁻¹ else 0) := by
    intro k _
    by_cases hk : k > 0
    · simp only [dif_pos hk]
      exact le_of_lt (inv_pos.mpr (Nat.cast_pos.mpr hk))
    · simp only [dif_neg hk, le_refl]
  have hval : (if h : (a : ℕ) > 0 then ((a : ℕ) : ℚ)⁻¹ else 0) = (a : ℚ)⁻¹ := by
    simp only [dif_pos (PNat.pos a)]
  calc (a : ℚ)⁻¹
      = (if h : (a : ℕ) > 0 then ((a : ℕ) : ℚ)⁻¹ else 0) := hval.symm
    _ ≤ ∑ n ∈ Finset.Icc (a : ℕ) (b : ℕ),
          if h : n > 0 then (n : ℚ)⁻¹ else 0 := Finset.single_le_sum hnn hmem

/- ## Part VII: Summary -/

/--
**Erdős Problem #288: Summary**

PROBLEM: Are there only finitely many pairs of intervals (I₁, I₂)
such that Σ_{I₁} 1/n + Σ_{I₂} 1/n ∈ ℕ?

STATUS: OPEN

EXAMPLES:
- [3,6] ∪ [20,20] gives 1/3 + 1/4 + 1/5 + 1/6 + 1/20 = 1
- [2,3] ∪ [6,6] gives 1/2 + 1/3 + 1/6 = 1
- [1,3] ∪ [6,6] gives 1 + 1/2 + 1/3 + 1/6 = 2

VARIANTS:
- Open even when |I₂| = 1
- Perhaps true for k intervals (any k)
-/
theorem erdos_288_statement :
    ErdosConjecture288 ↔ Set.Finite {p : IntervalPair | IsIntegerSum p} := by
  simp only [ErdosConjecture288, integerSumPairs]

/--
**Erdős Problem #288: Summary**

QUESTION: Are there only finitely many pairs of intervals (I₁, I₂) with
Σ_{I₁} 1/n + Σ_{I₂} 1/n ∈ ℕ?

STATUS: OPEN

KNOWN:
- Example: [3,6] ∪ [20,20] gives 1/3 + 1/4 + 1/5 + 1/6 + 1/20 = 1
- Example: [2,3] ∪ [6,6] gives 1/2 + 1/3 + 1/6 = 1
- Example: [1,3] ∪ [6,6] gives 1 + 1/2 + 1/3 + 1/6 = 2
- Open even when |I₂| = 1
- Conjectured to hold for k intervals (any k)
-/
theorem erdos_288_summary :
    ErdosConjecture288 ↔ Set.Finite {p : IntervalPair | IsIntegerSum p} :=
  erdos_288_statement

end Erdos288
