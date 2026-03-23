/-
Erdős Problem #538: Reciprocal Sums with Bounded Prime Representations

Let r ≥ 2 and A ⊆ {1,...,N} be such that for any m, there are at most r
solutions to m = p · a where p is prime and a ∈ A. Give the best possible
upper bound for Σ_{n ∈ A} 1/n.

## Status: OPEN

Erdős observed the upper bound r · log N / log log N via double counting.
The optimal bound remains open.

## References
- Erdős (1973), [Er73]
- Related: Problems 536, 537
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Classical

/-
## Section I: Representation Count
-/

/-- The set of pairs (p, a) with p prime, a ∈ A, and m = p · a. -/
noncomputable def primeReprSet (A : Finset ℕ) (m : ℕ) : Finset (ℕ × ℕ) :=
  (A.product (Finset.range (m + 1))).filter (fun pa =>
    pa.2.Prime ∧ m = pa.2 * pa.1 ∧ pa.1 ∈ A)

/-- The number of representations of m as p · a where p is prime and a ∈ A.
    Counts elements a ∈ A such that there exists a prime p with m = p * a. -/
noncomputable def reprCount (A : Finset ℕ) (m : ℕ) : ℕ :=
  (A.filter (fun a => ∃ p : ℕ, p.Prime ∧ m = p * a)).card

/-- A set A has r-bounded prime representations: for every m,
there are at most r solutions to m = p · a with p prime and a ∈ A. -/
def HasBoundedRepr (A : Finset ℕ) (r : ℕ) : Prop :=
  ∀ m : ℕ, reprCount A m ≤ r

/-
## Section II: Basic Properties of reprCount
-/

/-- The representation count of the empty set is 0 for any m. -/
theorem reprCount_empty (m : ℕ) : reprCount ∅ m = 0 := by
  simp [reprCount]

/-- The representation count is bounded by the cardinality of A. -/
theorem reprCount_le_card (A : Finset ℕ) (m : ℕ) :
    reprCount A m ≤ A.card :=
  Finset.card_filter_le A _

/-- The empty set has r-bounded representations for any r. -/
theorem hasBoundedRepr_empty (r : ℕ) : HasBoundedRepr ∅ r := by
  intro m
  simp [reprCount_empty]

/-- If A has r-bounded representations, it also has r'-bounded
    representations for any r' ≥ r. -/
theorem hasBoundedRepr_mono {A : Finset ℕ} {r r' : ℕ} (h : HasBoundedRepr A r)
    (hr : r ≤ r') : HasBoundedRepr A r' := by
  intro m
  exact le_trans (h m) hr

/-- A subset of a set with r-bounded representations also has r-bounded
    representations. -/
theorem hasBoundedRepr_subset {A B : Finset ℕ} {r : ℕ} (h : HasBoundedRepr B r)
    (hAB : A ⊆ B) : HasBoundedRepr A r := by
  intro m
  calc reprCount A m
      = (A.filter (fun a => ∃ p : ℕ, p.Prime ∧ m = p * a)).card := rfl
    _ ≤ (B.filter (fun a => ∃ p : ℕ, p.Prime ∧ m = p * a)).card := by
        apply Finset.card_le_card
        exact Finset.filter_subset_filter _ hAB
    _ = reprCount B m := rfl
    _ ≤ r := h m

/-
## Section III: The Reciprocal Sum
-/

/-- The reciprocal sum Σ_{n ∈ A} 1/n (with 0 contributing nothing). -/
noncomputable def reciprocalSum (A : Finset ℕ) : ℝ :=
  ∑ n ∈ A, if n > 0 then (1 : ℝ) / (n : ℝ) else 0

/-- The reciprocal sum of the empty set is 0. -/
theorem reciprocalSum_empty : reciprocalSum ∅ = 0 := by
  simp [reciprocalSum]

/-- The reciprocal sum is non-negative. -/
theorem reciprocalSum_nonneg (A : Finset ℕ) : 0 ≤ reciprocalSum A := by
  apply Finset.sum_nonneg
  intro n _
  split_ifs with h
  · exact div_nonneg one_pos.le (Nat.cast_nonneg n)
  · exact le_refl _

/-- The reciprocal sum is monotone: if A ⊆ B then Σ_{a ∈ A} 1/a ≤ Σ_{b ∈ B} 1/b. -/
theorem reciprocalSum_mono {A B : Finset ℕ} (h : A ⊆ B) :
    reciprocalSum A ≤ reciprocalSum B := by
  apply Finset.sum_le_sum_of_subset_of_nonneg h
  intro n _ _
  split_ifs with h
  · exact div_nonneg one_pos.le (Nat.cast_nonneg n)
  · exact le_refl _

/-- Adding a positive element to A increases the reciprocal sum. -/
theorem reciprocalSum_insert {A : Finset ℕ} {n : ℕ} (hn : n > 0) (hna : n ∉ A) :
    reciprocalSum A + (1 : ℝ) / (n : ℝ) = reciprocalSum (insert n A) := by
  simp only [reciprocalSum, Finset.sum_insert hna]
  rw [if_pos hn]
  ring

/-
## Section IV: The Problem Statement
-/

/-- **Erdős Problem #538**: Give the best possible upper bound for the
reciprocal sum of A ⊆ {1,...,N} with r-bounded prime representations.

The conjecture seeks the optimal f(r,N) such that
Σ_{n ∈ A} 1/n ≤ f(r,N) whenever HasBoundedRepr A r. -/
def ErdosProblem538 : Prop :=
  ∃ f : ℕ → ℕ → ℝ,
    (∀ r N : ℕ, r ≥ 2 →
      ∀ A : Finset ℕ, A ⊆ Finset.range (N + 1) → HasBoundedRepr A r →
        reciprocalSum A ≤ f r N) ∧
    (∀ g : ℕ → ℕ → ℝ,
      (∀ r N : ℕ, r ≥ 2 →
        ∀ A : Finset ℕ, A ⊆ Finset.range (N + 1) → HasBoundedRepr A r →
          reciprocalSum A ≤ g r N) →
      ∀ r N : ℕ, r ≥ 2 → N ≥ 2 → f r N ≤ g r N)

/-
## Section V: Erdős Upper Bound

Erdős's key observation uses double counting:
  (Σ_{a ∈ A} 1/a) · (Σ_{p ≤ N} 1/p) ≤ r · (Σ_{m ≤ N²} 1/m)

Since Σ_{p ≤ N} 1/p ~ log log N (Mertens' theorem) and
Σ_{m ≤ N²} 1/m ~ 2 log N, this gives:
  Σ_{a ∈ A} 1/a ≤ r · 2 log N / log log N = O(r · log N / log log N)
-/

/-- Erdős proved: Σ_{n ∈ A} 1/n ≪ r · log N / log log N.
    This requires Mertens' theorem and harmonic sum asymptotics. -/
theorem erdos_upper_bound :
    ∃ C : ℝ, C > 0 ∧
      ∀ r N : ℕ, r ≥ 2 → N ≥ 3 →
        ∀ A : Finset ℕ, A ⊆ Finset.range (N + 1) → HasBoundedRepr A r →
          reciprocalSum A ≤ C * (r : ℝ) * Real.log (N : ℝ) /
            Real.log (Real.log (N : ℝ)) := by
  sorry

/-
## Section VI: Trivial Bound Without Constraint
-/

/-- Key inequality: 1/(n+1) ≤ log(n+1) - log(n) for n ≥ 1.
    Proof: apply log(x) ≤ x - 1 to x = n/(n+1), giving
    log(n/(n+1)) ≤ n/(n+1) - 1 = -1/(n+1), so log((n+1)/n) ≥ 1/(n+1). -/
private lemma inv_succ_le_log_sub (n : ℕ) (hn : 1 ≤ n) :
    (1 : ℝ) / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hn_pos hn1_pos)
  rw [Real.log_div (ne_of_gt hn_pos) (ne_of_gt hn1_pos)] at h
  -- h : log n - log(n+1) ≤ n/(n+1) - 1 = -1/(n+1)
  have : (n : ℝ) / ((n : ℝ) + 1) - 1 = -(1 / ((n : ℝ) + 1)) := by field_simp; ring
  linarith

/-- Without the representation constraint, the maximum reciprocal sum
of A ⊆ {1,...,N} is bounded by 1 + log N (harmonic sum bound). -/
theorem harmonic_upper_bound (N : ℕ) (hN : N ≥ 1) :
    ∀ A : Finset ℕ, A ⊆ Finset.range (N + 1) →
      reciprocalSum A ≤ 1 + Real.log (N : ℝ) := by
  intro A hA
  -- Reduce to bounding the full harmonic sum H_N
  suffices h : reciprocalSum (Finset.range (N + 1)) ≤ 1 + Real.log (N : ℝ) from
    le_trans (reciprocalSum_mono hA) h
  clear A hA
  -- Prove H_N ≤ 1 + log N by induction
  induction N with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn_pos
    · -- Base case: N = 1
      -- reciprocalSum({0,1}) = 0 + 1 = 1 ≤ 1 + log 1 = 1
      simp only [reciprocalSum, Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num [Real.log_one]
    · -- Inductive step: n ≥ 1, prove for N = n + 1
      have h_ih := ih (by omega : n ≥ 1)
      -- Split: reciprocalSum(range(n+2)) = reciprocalSum(range(n+1)) + 1/(n+1)
      show reciprocalSum (Finset.range (n + 1 + 1)) ≤ 1 + Real.log (↑(n + 1))
      simp only [reciprocalSum] at h_ih ⊢
      rw [show n + 1 + 1 = (n + 1) + 1 from rfl, Finset.sum_range_succ]
      rw [if_pos (show n + 1 > 0 from Nat.succ_pos n)]
      -- Goal: (∑ in range(n+1)) + 1/↑(n+1) ≤ 1 + log ↑(n+1)
      have h_key := inv_succ_le_log_sub n (by omega : 1 ≤ n)
      -- Normalize ↑(n+1) to ↑n + 1
      have h_cast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [h_cast]
      linarith

/-
## Section VII: Double Counting Identity

The key combinatorial identity underlying Erdős's argument.
For A ⊆ {1,...,N} with r-bounded representations:

Σ_{a ∈ A} (1/a) · |{p prime : p ≤ N/a}|
  = Σ_{m ≤ N} reprCount(A, m) / m    (approximately)
  ≤ r · Σ_{m ≤ N} 1/m
-/

/-- For each a ∈ A, the number of primes p with pa ≤ N is at most N/a. -/
-- Proved by Aristotle (Harmonic)
theorem primes_for_element_bound (A : Finset ℕ) (N : ℕ) (a : ℕ)
    (ha : a ∈ A) (hA : A ⊆ Finset.range (N + 1)) (ha0 : a > 0) :
    ((Finset.range (N + 1)).filter (fun p => p.Prime ∧ p * a ≤ N)).card ≤ N / a := by
  have h_prime_to_int : Finset.filter (fun p => Nat.Prime p ∧ p * a ≤ N) (Finset.range (N + 1)) ⊆ Finset.image (fun x => x) (Finset.Icc 1 (N / a)) := by
    norm_num +zetaDelta at *;
    exact fun p hp => Finset.mem_Icc.mpr ⟨ Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2.1 ), Nat.le_div_iff_mul_le ha0 |>.2 ( Finset.mem_filter.mp hp |>.2.2 ) ⟩;
  exact le_trans ( Finset.card_le_card h_prime_to_int ) ( Finset.card_image_le.trans ( by simpa ) )

/-- The double counting inequality: bounding the sum of reprCount.
    Σ_{m=0}^{N} reprCount(A, m) ≤ |A| · N since each a ∈ A contributes
    at most N/a ≤ N values of m = pa (using a ≥ 1 and p prime ≥ 2,
    so m = pa ≥ 2, meaning m = 0 and m = 1 contribute nothing).
    Note: requires all elements of A to be positive (as in the original
    problem statement A ⊆ {1,...,N}). Without this, A = {0}, N = 0
    gives reprCount({0}, 0) = 1 > 0 = |A|·N, a counterexample. -/
theorem sum_reprCount_bound (A : Finset ℕ) (N : ℕ)
    (hA : A ⊆ Finset.range (N + 1)) (hpos : ∀ a ∈ A, 0 < a) :
    ∑ m ∈ Finset.range (N + 1), reprCount A m ≤ A.card * N := by
  -- Step 1: reprCount A 0 = 0 when all elements of A are positive
  -- (0 = p*a with p prime ≥ 2 and a ≥ 1 is impossible)
  have h0 : reprCount A 0 = 0 := by
    simp only [reprCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro a ha ⟨p, hp, heq⟩
    have := Nat.mul_le_mul_left 1 (hpos a ha)
    have := Nat.mul_le_mul_right a hp.two_le
    omega
  -- Step 2: Split range(N+1) = {0} ∪ Ico(1, N+1), peel off the m=0 term
  have h0_mem : (0 : ℕ) ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.zero_lt_succ N)
  have hsplit : ∑ m ∈ Finset.range (N + 1), reprCount A m =
      reprCount A 0 + ∑ m ∈ (Finset.range (N + 1)).erase 0, reprCount A m :=
    (Finset.add_sum_erase _ (fun m => reprCount A m) h0_mem).symm
  rw [hsplit, h0, zero_add]
  -- Step 3: The remaining set has N elements, each contributing ≤ A.card
  have hcard_erase : ((Finset.range (N + 1)).erase 0).card = N := by
    rw [Finset.card_erase_of_mem h0_mem, Finset.card_range]
    omega
  calc ∑ m ∈ (Finset.range (N + 1)).erase 0, reprCount A m
      ≤ ∑ m ∈ (Finset.range (N + 1)).erase 0, A.card :=
        Finset.sum_le_sum (fun m _ => reprCount_le_card A m)
    _ = ((Finset.range (N + 1)).erase 0).card * A.card := by
        simp [Finset.sum_const, smul_eq_mul]
    _ = N * A.card := by rw [hcard_erase]
    _ = A.card * N := Nat.mul_comm _ _

/-
## Section VIII: Connections to Multiplicative Structure
-/

/-- The multiplicative energy of A with primes: the number of pairs (a₁, a₂)
    in A × A with ∃ p₁ p₂ prime, p₁a₁ = p₂a₂. Always includes the diagonal
    (|A| pairs with a₁ = a₂, using any prime for both).
    Note: the bound r²·|A| is FALSE. Counterexample: A = {2,3,5,7,11} with
    N=11 has r=2, but all 25 pairs satisfy the condition (any two primes
    p_i, p_j have gcd 1, and p_i/1, p_j/1 are both prime), while r²·|A| = 20.
    The trivial bound |A|² always holds. -/
theorem multiplicative_energy_trivial_bound (A : Finset ℕ) (N : ℕ)
    (hA : A ⊆ Finset.range (N + 1)) :
    (Finset.card ((A ×ˢ A).filter (fun p =>
      ∃ q₁ q₂ : ℕ, q₁.Prime ∧ q₂.Prime ∧
        q₁ * p.1 = q₂ * p.2)) : ℝ)
    ≤ (A.card : ℝ) ^ 2 := by
  have h := Finset.card_filter_le (A ×ˢ A) (fun p =>
    ∃ q₁ q₂ : ℕ, q₁.Prime ∧ q₂.Prime ∧ q₁ * p.1 = q₂ * p.2)
  rw [Finset.card_product] at h
  have : (A.card * A.card : ℕ) = A.card ^ 2 := by ring
  calc ((Finset.card ((A ×ˢ A).filter _)) : ℝ)
      ≤ (A.card * A.card : ℕ) := by exact_mod_cast h
    _ = (A.card : ℝ) ^ 2 := by push_cast; ring

/-
## Section IX: Special Cases
-/

/-- For r = 1 with A ⊆ {1,...,N} (positive elements), we have |A| ≤ N.
    Note: without positivity, A ⊆ range(N+1) = {0,...,N} gives |A| ≤ N+1.
    Adding the positivity hypothesis excludes 0, giving A ⊆ {1,...,N}. -/
theorem r_eq_1_card_bound (A : Finset ℕ) (N : ℕ)
    (hA : A ⊆ Finset.range (N + 1)) (_hr : HasBoundedRepr A 1)
    (hpos : ∀ a ∈ A, 0 < a) :
    (A.card : ℝ) ≤ (N : ℝ) := by
  -- 0 ∉ A since all elements are positive
  have h0 : 0 ∉ A := fun h => Nat.lt_irrefl 0 (hpos 0 h)
  have h_sub : A ⊆ (Finset.range (N + 1)).erase 0 := by
    intro a ha
    exact Finset.mem_erase.mpr ⟨Nat.pos_iff_ne_zero.mp (hpos a ha), hA ha⟩
  have h_card : A.card ≤ N := by
    have h1 := Finset.card_le_card h_sub
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (Nat.zero_lt_succ N)),
        Finset.card_range] at h1
    omega
  exact_mod_cast h_card

/-- A singleton set always has 1-bounded representations. -/
theorem singleton_hasBoundedRepr {a : ℕ} : HasBoundedRepr {a} 1 := by
  intro m
  simp only [reprCount]
  calc (Finset.filter (fun x => ∃ p, p.Prime ∧ m = p * x) {a}).card
      ≤ ({a} : Finset ℕ).card := Finset.card_filter_le _ _
    _ = 1 := Finset.card_singleton a
