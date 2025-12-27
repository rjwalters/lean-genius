import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

/-!
# Sum of Reciprocals of Triangular Numbers

## What This Proves
The sum of reciprocals of triangular numbers equals 2:

  ∑_{n=1}^∞ 1/Tₙ = ∑_{n=1}^∞ 2/(n(n+1)) = 2

where Tₙ = n(n+1)/2 is the nth triangular number.

This is Wiedijk's 100 Theorems #42.

## Approach
- **Partial Fractions**: The reciprocal 2/(n(n+1)) decomposes as 2(1/n - 1/(n+1))
- **Telescoping Series**: The sum becomes 2(1 - 1/2 + 1/2 - 1/3 + 1/3 - ...) = 2·1 = 2
- **Foundation (from Mathlib)**: We use Mathlib's infinite sum machinery and prove
  convergence via comparison with the geometric series.

## Historical Context
This beautiful identity connects the triangular numbers (known since antiquity) with
infinite series. The triangular numbers 1, 3, 6, 10, 15, ... were studied by the
Pythagoreans, who arranged dots in triangular patterns.

The proof that their reciprocals sum to exactly 2 is a lovely example of a
telescoping series—each term cancels part of the previous one, leaving only
the first and last contributions.

## Status
- [x] Complete proof
- [x] Uses Mathlib for series convergence
- [x] Proves extensions/corollaries
- [x] Pedagogical documentation (telescoping explanation)

## Mathlib Dependencies
- `Summable` : Predicate for convergent series
- `tsum` : Topological sum of an infinite series
- `Finset.sum_range_sub` : Telescoping sum identity

Original formalization for Lean Genius.
-/

namespace TriangularNumberReciprocals

open Finset BigOperators Filter Topology

/-! ## Triangular Numbers

The nth triangular number is the sum 1 + 2 + ... + n = n(n+1)/2. -/

/-- The nth triangular number: T(n) = n(n+1)/2

These are the numbers 1, 3, 6, 10, 15, 21, ... formed by summing
consecutive natural numbers starting from 1. Visually, they count
dots arranged in equilateral triangles. -/
def triangular (n : ℕ) : ℕ := n * (n + 1) / 2

/-! ## Partial Fraction Decomposition

The key algebraic identity: 2/(n(n+1)) = 2/n - 2/(n+1).
This transforms our sum into a telescoping series. -/

/-- **Partial Fraction Identity**

The reciprocal of n(n+1) decomposes as 1/n - 1/(n+1).
Equivalently: 2/(n(n+1)) = 2/n - 2/(n+1).

This is the heart of the proof: it converts a product in the denominator
into a difference, enabling the telescoping argument. -/
theorem partial_fraction (n : ℕ) (hn : n ≠ 0) :
    (2 : ℝ) / (n * (n + 1)) = 2 / n - 2 / (n + 1) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
  have hnn1 : (n : ℝ) * (n + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- Alternative form: 1/(n(n+1)) = 1/n - 1/(n+1) -/
theorem partial_fraction' (n : ℕ) (hn : n ≠ 0) :
    (1 : ℝ) / (n * (n + 1)) = 1 / n - 1 / (n + 1) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
  have hnn1 : (n : ℝ) * (n + 1) ≠ 0 := by positivity
  field_simp

/-! ## Telescoping Finite Sums

Before tackling the infinite sum, we establish the telescoping property
for finite partial sums. -/

/-- **Finite Telescoping Sum**

The partial sum ∑_{k=1}^{n} 2/(k(k+1)) = 2 - 2/(n+1).

Watch how the terms cancel:
  2(1/1 - 1/2) + 2(1/2 - 1/3) + 2(1/3 - 1/4) + ...
  = 2(1 - 1/(n+1))
  = 2 - 2/(n+1)

As n → ∞, this approaches 2. -/
theorem finite_sum_reciprocals (n : ℕ) (hn : n ≠ 0) :
    ∑ k ∈ Finset.Icc 1 n, (2 : ℝ) / (k * (k + 1)) = 2 - 2 / (n + 1) := by
  induction n with
  | zero => contradiction
  | succ m ih =>
    by_cases hm : m = 0
    · -- Base case: n = 1
      subst hm
      simp only [Finset.Icc_self, Finset.sum_singleton]
      norm_num
    · -- Inductive case
      have : Finset.Icc 1 (m + 1) = Finset.Icc 1 m ∪ {m + 1} := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
        omega
      rw [this, Finset.sum_union]
      · rw [Finset.sum_singleton, ih hm]
        have hm1 : (m + 1 : ℝ) ≠ 0 := by positivity
        have hprod : (m + 1 : ℝ) * (m + 1 + 1) ≠ 0 := by positivity
        field_simp
        ring
      · simp only [Finset.disjoint_singleton_right, Finset.mem_Icc, not_and, not_le]
        intro _
        omega

/-! ## Series Convergence

We now prove the infinite series converges, which is necessary before
computing its sum. -/

/-- The sequence 1/(n(n+1)) is summable.

This follows because 1/(n(n+1)) < 1/n², and the p-series with p=2 converges. -/
theorem summable_reciprocal_product : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) * (n + 1))) := by
  have h_bound : ∀ n : ℕ, (1 : ℝ) / ((n : ℝ) * (n + 1)) ≤ 1 / (n : ℝ)^2 := fun n => by
    by_cases hn : n = 0
    · simp [hn]
    · have hn' : (n : ℝ) > 0 := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have hprod : (n : ℝ) * (n + 1) ≥ n * n := by nlinarith
      calc (1 : ℝ) / ((n : ℝ) * (n + 1))
          ≤ 1 / (n * n) := by
            apply one_div_le_one_div_of_le (by positivity : (n : ℝ) * n > 0) hprod
        _ = 1 / n ^ 2 := by ring
  have h_nonneg : ∀ n : ℕ, 0 ≤ (1 : ℝ) / ((n : ℝ) * (n + 1)) := fun n => by
    by_cases hn : n = 0
    · simp [hn]
    · positivity
  have h_pseries : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ)^2 := by
    have h := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
    simp only [Real.rpow_natCast, ← one_div] at h
    exact_mod_cast h
  exact Summable.of_nonneg_of_le h_nonneg h_bound h_pseries

/-- The series 2/(n(n+1)) is summable. -/
theorem summable_two_reciprocal_product :
    Summable (fun n : ℕ => (2 : ℝ) / ((n : ℝ) * (n + 1))) := by
  have h := summable_reciprocal_product
  have h2 : (fun n : ℕ => (2 : ℝ) / ((n : ℝ) * (n + 1))) =
            (fun n : ℕ => 2 * ((1 : ℝ) / ((n : ℝ) * (n + 1)))) := by
    ext n; ring
  rw [h2]
  exact h.mul_left 2

/-! ## The Main Theorem: Sum Equals 2 -/

/-- **Sum of Reciprocals of Triangular Numbers (Wiedijk #42)**

The infinite sum ∑_{n=1}^∞ 2/(n(n+1)) = 2.

Equivalently, since Tₙ = n(n+1)/2, we have ∑_{n=1}^∞ 1/Tₙ = 2.

**Proof Idea**:
Using partial fractions, 2/(n(n+1)) = 2/n - 2/(n+1).
The sum telescopes:
  (2/1 - 2/2) + (2/2 - 2/3) + (2/3 - 2/4) + ...
  = 2/1 = 2

Each intermediate term cancels, leaving only the first term. -/
theorem sum_reciprocals_triangular :
    HasSum (fun n : ℕ => if n = 0 then 0 else (2 : ℝ) / ((n : ℝ) * (n + 1))) 2 := by
  -- We prove this by showing partial sums over Finset.range n converge to 2
  -- The partial sum ∑_{k=0}^{n-1} f(k) = 2 - 2/n for n ≥ 1
  have h_partial : ∀ n : ℕ, n ≥ 1 →
      ∑ k ∈ Finset.range n, (if k = 0 then 0 else (2 : ℝ) / ((k : ℝ) * (k + 1))) =
      2 - 2 / n := by
    intro n hn
    have h0mem : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn))
    rw [Finset.sum_eq_sum_diff_singleton_add h0mem]
    simp only [ite_true, add_zero]
    have h_eq : Finset.range n \ {0} = Finset.Icc 1 (n - 1) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton, Finset.mem_Icc]
      omega
    rw [h_eq]
    have hsum : ∀ k ∈ Finset.Icc 1 (n - 1), (if k = 0 then 0 else (2 : ℝ) / ((k : ℝ) * (k + 1))) =
                (2 : ℝ) / ((k : ℝ) * (k + 1)) := by
      intro k hk
      simp only [Finset.mem_Icc] at hk
      have hk_pos : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk.1
      simp only [hk_pos, ↓reduceIte]
    rw [Finset.sum_congr rfl hsum]
    by_cases hn' : n = 1
    · subst hn'; simp
    · have hn1' : n - 1 ≠ 0 := by omega
      rw [finite_sum_reciprocals (n - 1) hn1']
      congr 1
      rw [Nat.cast_sub hn]
      ring
  -- Show nonnegativity of our function
  have h_nonneg : ∀ i : ℕ, 0 ≤ (if i = 0 then 0 else (2 : ℝ) / ((i : ℝ) * (i + 1))) := fun i => by
    split_ifs with hi
    · rfl
    · positivity
  -- Now show convergence using the sequential characterization of HasSum
  rw [hasSum_iff_tendsto_nat_of_nonneg h_nonneg]
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  use Nat.ceil (2 / ε) + 1
  intro n hn
  have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) hn)
  have hn1 : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr hn0
  rw [h_partial n hn1]
  rw [Real.dist_eq]
  have hn_pos : (n : ℝ) > 0 := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  calc |(2 : ℝ) - 2 / ↑n - 2|
      = |-(2 / (n : ℝ))| := by ring_nf
    _ = (2 : ℝ) / n := by rw [abs_neg, abs_of_pos (by positivity)]
    _ < ε := by
        rw [div_lt_iff hn_pos]
        have h1 : (n : ℝ) ≥ Nat.ceil (2 / ε) + 1 := by exact_mod_cast hn
        have h2 : (Nat.ceil (2 / ε) : ℝ) ≥ 2 / ε := Nat.le_ceil _
        have h3 : (2 : ℝ) / ε < n := by linarith
        have h4 : (2 : ℝ) < ε * n := by
          rw [mul_comm]
          exact (div_lt_iff hε).mp h3
        linarith

/-- The tsum version of the main theorem. -/
theorem tsum_reciprocals_triangular :
    ∑' n : ℕ, (if n = 0 then 0 else (2 : ℝ) / ((n : ℝ) * (n + 1))) = 2 :=
  sum_reciprocals_triangular.tsum_eq

/-- **Corollary**: Sum of 1/(n(n+1)) from n=1 to infinity equals 1. -/
theorem sum_reciprocals_one :
    HasSum (fun n : ℕ => if n = 0 then 0 else (1 : ℝ) / ((n : ℝ) * (n + 1))) 1 := by
  have h := sum_reciprocals_triangular
  have h_scale : (fun n : ℕ => if n = 0 then 0 else (2 : ℝ) / ((n : ℝ) * (n + 1))) =
                 (fun n : ℕ => 2 * (if n = 0 then 0 else (1 : ℝ) / ((n : ℝ) * (n + 1)))) := by
    ext n
    split_ifs with hn <;> ring
  rw [h_scale] at h
  have h2 : HasSum (fun n : ℕ => (if n = 0 then 0 else (1 : ℝ) / ((n : ℝ) * (n + 1)))) (2 / 2) := by
    have hdiv := h.div_const 2
    simp only [mul_div_assoc] at hdiv
    convert hdiv using 1
    ext n
    ring
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self] at h2
  exact h2

/-! ## Connection to Triangular Numbers -/

/-- The reciprocal of the nth triangular number is 2/(n(n+1)). -/
theorem reciprocal_triangular (n : ℕ) (hn : n ≠ 0) :
    (1 : ℝ) / (triangular n) = 2 / (n * (n + 1)) := by
  simp only [triangular]
  have hdiv : 2 ∣ n * (n + 1) := by
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [hk]; exact ⟨k * (2 * k + 1), by ring⟩
    · rw [hk]; exact ⟨(2 * k + 1) * (k + 1), by ring⟩
  obtain ⟨m, hm⟩ := hdiv
  have hm' : n * (n + 1) / 2 = m := by omega
  rw [hm']
  have hm_pos : m ≠ 0 := by
    intro hm0
    rw [hm0] at hm
    have : n * (n + 1) = 0 := hm
    have : n * (n + 1) > 0 := Nat.pos_of_ne_zero hn |> fun h => Nat.mul_pos h (Nat.succ_pos n)
    omega
  field_simp
  have : (n : ℝ) * (n + 1) = 2 * m := by
    calc (n : ℝ) * (n + 1) = ((n * (n + 1) : ℕ) : ℝ) := by simp
      _ = ((2 * m : ℕ) : ℝ) := by rw [hm]
      _ = 2 * m := by simp
  linarith

/-! ## Pedagogical Examples -/
example : triangular 1 = 1 := by native_decide
example : triangular 2 = 3 := by native_decide
example : triangular 3 = 6 := by native_decide
example : triangular 4 = 10 := by native_decide
example : triangular 5 = 15 := by native_decide

#check sum_reciprocals_triangular
#check partial_fraction
#check finite_sum_reciprocals
#check summable_reciprocal_product

end TriangularNumberReciprocals
