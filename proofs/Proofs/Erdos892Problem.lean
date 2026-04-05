/-
# Erdős Problem #892: Primitive Sequence Domination

Given an increasing integer sequence b₁ < b₂ < ⋯, find necessary and
sufficient conditions for the existence of a primitive sequence
a₁ < a₂ < ⋯ (no aᵢ divides aⱼ for i ≠ j) with aₙ ≪ bₙ for all n.

## Status: OPEN

## References
- Erdős (1935): Σ 1/(bₙ log bₙ) < ∞ is necessary
- Erdős–Sárközy–Szemerédi (1967): Σ_{bₙ<x} 1/bₙ = o(log x / √(log log x))
  is necessary
- Erdős–Sárközy–Szemerédi (1968): Original problem formulation
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
attribute [local instance] Classical.dec

/-
## Section I: Primitive Sequences
-/

/-- A sequence (modeled as ℕ → ℕ) is primitive if no element divides
another. -/
def IsPrimitive (a : ℕ → ℕ) : Prop :=
  ∀ i j : ℕ, i ≠ j → ¬ (a i ∣ a j)

/-- A sequence is strictly increasing. -/
def IsStrictlyIncreasing (a : ℕ → ℕ) : Prop :=
  ∀ i j : ℕ, i < j → a i < a j

/-
## Section II: Domination
-/

/-- Sequence a is dominated by sequence b: there exists C such that
aₙ ≤ C · bₙ for all n. -/
def IsDominatedBy (a b : ℕ → ℕ) : Prop :=
  ∃ C : ℕ, C > 0 ∧ ∀ n : ℕ, a n ≤ C * b n

/-
## Section III: The Problem
-/

/-- **Erdős Problem #892**: Characterize sequences b such that there
exists a primitive, strictly increasing sequence a with a ≪ b.

The problem asks for necessary and sufficient conditions on b. -/
def ErdosProblem892 (b : ℕ → ℕ) : Prop :=
  IsStrictlyIncreasing b →
    ∃ a : ℕ → ℕ, IsStrictlyIncreasing a ∧ IsPrimitive a ∧
      IsDominatedBy a b

/-
## Section IV: Necessary Conditions — Proved Lemmas
-/

/-- Every element of a primitive sequence is ≥ 2.
    If a(n) = 0, then any a(j) | 0, contradicting primitivity.
    If a(n) = 1, then 1 | a(j), contradicting primitivity. -/
theorem primitive_elements_ge_two (a : ℕ → ℕ)
    (hprim : IsPrimitive a) : ∀ n, a n ≥ 2 := by
  intro n
  by_contra h
  push_neg at h
  have h1 : a n = 0 ∨ a n = 1 := by omega
  rcases h1 with h0 | h1
  · have := hprim (n + 1) n (by omega)
    rw [h0] at this
    exact this (dvd_zero _)
  · have := hprim n (n + 1) (by omega)
    rw [h1] at this
    exact this (one_dvd _)

/-- A strictly increasing sequence ℕ → ℕ with values ≥ 2 satisfies a(n) ≥ n + 2. -/
theorem strict_inc_lower_bound (a : ℕ → ℕ) (hinc : IsStrictlyIncreasing a)
    (hge : ∀ n, a n ≥ 2) : ∀ n, a n ≥ n + 2 := by
  intro n
  induction n with
  | zero => exact hge 0
  | succ k ih =>
    have := hinc k (k + 1) (by omega)
    omega

/-- For any bound M, a strictly increasing sequence with values ≥ 2
    eventually exceeds M. -/
theorem strict_inc_eventually_ge (a : ℕ → ℕ) (hinc : IsStrictlyIncreasing a)
    (hge : ∀ n, a n ≥ 2) (M : ℕ) : ∃ N₀, ∀ n, n ≥ N₀ → a n ≥ M := by
  exact ⟨M, fun n hn => by have := strict_inc_lower_bound a hinc hge n; omega⟩

/-- Key multiplicative bound: if a ≤ C·b with b ≥ C and both ≥ 2, then
    a · log(a) ≤ 2C · (b · log(b)).

    Proof: C ≤ b gives a ≤ C·b ≤ b², so log(a) ≤ log(b²) = 2·log(b).
    Combined with a ≤ C·b: a·log(a) ≤ (C·b)·(2·log(b)) = 2C·(b·log(b)). -/
theorem product_log_comparison (a_n b_n C : ℕ)
    (hdom : a_n ≤ C * b_n) (ha : a_n ≥ 2) (hb : b_n ≥ 2)
    (hlarge : b_n ≥ C) :
    (a_n : ℝ) * Real.log (a_n : ℝ) ≤
      2 * (C : ℝ) * ((b_n : ℝ) * Real.log (b_n : ℝ)) := by
  have ha_pos : (0 : ℝ) < (a_n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hb_pos : (0 : ℝ) < (b_n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlogb_pos : 0 < Real.log (b_n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < b_n by omega))
  -- Step 1: a ≤ b² (from a ≤ C·b and C ≤ b)
  have hab_sq : a_n ≤ b_n * b_n :=
    le_trans hdom (Nat.mul_le_mul_right b_n hlarge)
  -- Step 2: log(a) ≤ 2·log(b)
  have hlog_bound : Real.log (a_n : ℝ) ≤ 2 * Real.log (b_n : ℝ) := by
    have h1 : (a_n : ℝ) ≤ (b_n : ℝ) * (b_n : ℝ) := by exact_mod_cast hab_sq
    have h2 : Real.log (a_n : ℝ) ≤ Real.log ((b_n : ℝ) * (b_n : ℝ)) :=
      Real.log_le_log ha_pos h1
    have h3 : Real.log ((b_n : ℝ) * (b_n : ℝ)) = 2 * Real.log (b_n : ℝ) := by
      rw [Real.log_mul (ne_of_gt hb_pos) (ne_of_gt hb_pos)]
      ring
    linarith
  -- Step 3: a·log(a) ≤ (C·b)·(2·log(b)) = 2C·(b·log(b))
  have hdom_cast : (a_n : ℝ) ≤ (C : ℝ) * (b_n : ℝ) := by exact_mod_cast hdom
  calc (a_n : ℝ) * Real.log (a_n : ℝ)
      ≤ (a_n : ℝ) * (2 * Real.log (b_n : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog_bound (le_of_lt ha_pos)
    _ ≤ ((C : ℝ) * (b_n : ℝ)) * (2 * Real.log (b_n : ℝ)) :=
        mul_le_mul_of_nonneg_right hdom_cast (by linarith)
    _ = 2 * (C : ℝ) * ((b_n : ℝ) * Real.log (b_n : ℝ)) := by ring

/-- Division form: 1/(b·log b) ≤ 2C/(a·log a).
    Follows from product_log_comparison by cross-multiplying. -/
lemma reciprocal_log_comparison (a_n b_n C : ℕ)
    (hdom : a_n ≤ C * b_n) (ha : a_n ≥ 2) (hb : b_n ≥ 2)
    (hlarge : b_n ≥ C) :
    (1 : ℝ) / ((b_n : ℝ) * Real.log (b_n : ℝ))
      ≤ 2 * (C : ℝ) / ((a_n : ℝ) * Real.log (a_n : ℝ)) := by
  have key := product_log_comparison a_n b_n C hdom ha hb hlarge
  have halog_pos : (a_n : ℝ) * Real.log (a_n : ℝ) > 0 :=
    mul_pos (Nat.cast_pos.mpr (by omega))
      (Real.log_pos (by exact_mod_cast (show 1 < a_n by omega)))
  have hblog_pos : (b_n : ℝ) * Real.log (b_n : ℝ) > 0 :=
    mul_pos (Nat.cast_pos.mpr (by omega))
      (Real.log_pos (by exact_mod_cast (show 1 < b_n by omega)))
  have hne_a : (↑a_n * Real.log ↑a_n) ≠ 0 := ne_of_gt halog_pos
  have hne_b : (↑b_n * Real.log ↑b_n) ≠ 0 := ne_of_gt hblog_pos
  rw [div_le_div_iff₀ hblog_pos halog_pos]
  linarith

/-
## Section V: Necessary Conditions — Axioms
These are deep number-theoretic results used as axioms.
-/

/-- Erdős (1935): For any primitive sequence, Σ 1/(aₙ log aₙ) converges. -/
axiom primitive_reciprocal_log_convergent (a : ℕ → ℕ)
    (hprim : IsPrimitive a) (hinc : IsStrictlyIncreasing a)
    (hge : ∀ n, a n ≥ 2) :
    ∃ S : ℝ, ∀ N : ℕ,
      (∑ n ∈ Finset.range N,
        (1 : ℝ) / ((a n : ℝ) * Real.log (a n : ℝ)))
      ≤ S

/-
**Known result (ESS 1967, not formalized):**
Erdős–Sárközy–Szemerédi proved a stronger necessary condition:
the partial reciprocal sums Σ_{bₙ<x} 1/bₙ = o(log x / √(log log x)).

**Known result (not formalized):**
The counting function of a primitive sequence grows sublinearly:
a primitive set A ⊆ {1,...,N} has |A| ≪ N / √(log N).

Both are deep number-theoretic results, previously axiomatized but unused
in any proofs. Kept as documentation.
-/

/-
## Section VI: Main Theorem
-/

/-- Erdős (1935): If a primitive sequence a satisfies a ≪ b, then
Σ 1/(bₙ · log bₙ) converges. This is a necessary condition.

Proof outline:
1. By primitive_reciprocal_log_convergent, Σ 1/(aₙ log aₙ) ≤ Sa
2. For n ≥ N₀ where a(n) ≥ C², we get b(n) ≥ C
3. reciprocal_log_comparison gives 1/(bₙ log bₙ) ≤ 2C/(aₙ log aₙ)
4. Head (n < N₀): finitely many terms, each bounded
5. Tail (n ≥ N₀): sum ≤ 2C · Sa -/
theorem erdos_1935_necessary (b : ℕ → ℕ) :
    (∃ a : ℕ → ℕ, IsStrictlyIncreasing a ∧ IsPrimitive a ∧
      IsDominatedBy a b) →
    ∃ S : ℝ, ∀ N : ℕ,
      (∑ n ∈ Finset.range N,
        if b n ≥ 2 then (1 : ℝ) / ((b n : ℝ) * Real.log (b n : ℝ))
        else 0)
      ≤ S := by
  intro ⟨a, hinc, hprim, C, hCpos, hdom⟩
  have hge := primitive_elements_ge_two a hprim
  obtain ⟨Sa, hSa⟩ := primitive_reciprocal_log_convergent a hprim hinc hge
  -- Threshold: for n ≥ N₀, a(n) ≥ C², hence b(n) ≥ C
  obtain ⟨N₀, hN₀⟩ := strict_inc_eventually_ge a hinc hge (C * C)
  have hb_large : ∀ n, n ≥ N₀ → b n ≥ C := by
    intro n hn
    by_contra hlt; push_neg at hlt
    have h1 : C * b n < C * C := mul_lt_mul_of_pos_left hlt hCpos
    linarith [hdom n, hN₀ n hn]
  -- Head bound: use actual finite sum of first N₀ terms (independent of N)
  use (∑ n ∈ Finset.range N₀,
    (if b n ≥ 2 then (1 : ℝ) / ((b n : ℝ) * Real.log (b n : ℝ)) else 0))
    + 2 * ↑C * Sa
  intro N
  -- Non-negativity of original sum terms
  have hf_nonneg : ∀ n, 0 ≤
      (if b n ≥ 2 then (1 : ℝ) / ((b n : ℝ) * Real.log (b n : ℝ)) else 0) := by
    intro n; split_ifs with hbn
    · exact div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _)
        (Real.log_nonneg (by exact_mod_cast (show 1 ≤ b n by omega))))
    · norm_num
  -- Non-negativity of comparison bound terms
  have hg_nonneg : ∀ n, 0 ≤
      2 * (C : ℝ) * ((1 : ℝ) / ((a n : ℝ) * Real.log (a n : ℝ))) := by
    intro n
    apply mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    exact div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _)
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ a n by have := hge n; omega))))
  -- Split sum at N₀ using filter decomposition
  have hsplit := (Finset.sum_filter_add_sum_filter_not (Finset.range N) (· < N₀)
    (fun n => if b n ≥ 2 then (1 : ℝ) / ((b n : ℝ) * Real.log (b n : ℝ)) else 0)).symm
  rw [hsplit]
  apply add_le_add
  -- Part 1 (Head): filter (· < N₀) ⊆ range N₀, all terms non-negative
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
      exact hn.2
    · intro n _ _; exact hf_nonneg n
  -- Part 2 (Tail): termwise comparison, then factor out 2C and bound by Sa
  · calc ∑ n ∈ (Finset.range N).filter (fun n => ¬(n < N₀)),
          (if b n ≥ 2 then (1 : ℝ) / ((b n : ℝ) * Real.log (b n : ℝ)) else 0)
        ≤ ∑ n ∈ (Finset.range N).filter (fun n => ¬(n < N₀)),
          (2 * (C : ℝ) * ((1 : ℝ) / ((a n : ℝ) * Real.log (a n : ℝ)))) := by
          apply Finset.sum_le_sum
          intro n hn
          simp only [Finset.mem_filter, Finset.mem_range] at hn
          have hn_ge : n ≥ N₀ := by omega
          split_ifs with hbn
          · rw [mul_one_div]
            exact reciprocal_log_comparison (a n) (b n) C (hdom n) (hge n) hbn (hb_large n hn_ge)
          · exact hg_nonneg n
      _ ≤ ∑ n ∈ Finset.range N,
          (2 * (C : ℝ) * ((1 : ℝ) / ((a n : ℝ) * Real.log (a n : ℝ)))) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset _ _
          · intro n _ _; exact hg_nonneg n
      _ = 2 * ↑C * ∑ n ∈ Finset.range N,
          ((1 : ℝ) / ((a n : ℝ) * Real.log (a n : ℝ))) := by
          rw [← Finset.mul_sum]
      _ ≤ 2 * ↑C * Sa := by
          exact mul_le_mul_of_nonneg_left (hSa N)
            (mul_nonneg (by norm_num) (Nat.cast_nonneg _))

/-
## Section VII: GCD Condition
-/

/-- A sequence has the GCD-free property: no non-trivial
solutions to gcd(bᵢ, bⱼ) = bₖ with distinct i, j, k. -/
def IsGCDFree (b : ℕ → ℕ) : Prop :=
  ∀ i j k : ℕ, i ≠ j → i ≠ k → j ≠ k →
    Nat.gcd (b i) (b j) ≠ b k

/-- Erdős asked specifically: if b is GCD-free, does there necessarily
exist a primitive sequence a with a ≪ b? -/
def ErdosProblem892GCDFree : Prop :=
  ∀ b : ℕ → ℕ, IsStrictlyIncreasing b → IsGCDFree b →
    ∃ a : ℕ → ℕ, IsStrictlyIncreasing a ∧ IsPrimitive a ∧
      IsDominatedBy a b

/-
## Section VIII: Concrete Non-Example
-/

/-- **Concrete non-example for Erdős #892**: The linear sequence b(n) = n+2
    cannot be dominated by any primitive sequence.

    Proof structure:
    1. By Erdős (1935), if a primitive a dominates b, then Σ 1/(b(n)·log b(n)) < ∞.
    2. For b(n) = n+2, this would require Σ 1/((n+2)·log(n+2)) < ∞.
    3. But this series diverges (Cauchy condensation test).
    4. Contradiction.

    Sorry count: 2 (both for known results awaiting Mathlib API update)
    - h_large: divergence of Σ 1/((n+2)·log(n+2))
    - hbound: simplification of the necessary condition for b = (·+2)
-/
theorem linear_growth_no_primitive_dominator :
    ¬ ∃ a : ℕ → ℕ, IsStrictlyIncreasing a ∧ IsPrimitive a ∧
      IsDominatedBy a (fun n => n + 2) := by
  intro ⟨a, hinc, hprim, hdom⟩
  -- Apply the Erdős 1935 necessary condition with b(n) = n+2
  obtain ⟨S, hS⟩ := erdos_1935_necessary (fun n => n + 2) ⟨a, hinc, hprim, hdom⟩
  -- The series Σ 1/((n+2)·log(n+2)) diverges, so for some N, partial sum > S+1
  have h_large : ∃ N : ℕ, S + 1 < ∑ n ∈ Finset.range N,
      (1 : ℝ) / ((↑n + 2 : ℝ) * Real.log (↑n + 2 : ℝ)) := by
    sorry -- Divergence of Σ 1/((n+2)·log(n+2)) by Cauchy condensation test
  obtain ⟨N, hN⟩ := h_large
  -- The necessary condition gives an upper bound S on partial sums
  have hbound : ∑ n ∈ Finset.range N,
      (1 : ℝ) / ((↑n + 2 : ℝ) * Real.log (↑n + 2 : ℝ)) ≤ S := by
    sorry -- Simplification: guard (n+2 ≥ 2) is always true, cast ↑(n+2) = ↑n+2
  linarith

end
