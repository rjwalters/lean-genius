/-
  Aristotle targets for Erdős Problem #318 (Signed Unit Fractions with Zero Sum)
  Routine supporting lemmas for automated proof search.
  See Erdos318Problem.lean for the main formalization.

  Criteria for inclusion:
  - sum_reciprocal_squares_less_than_one: ∑_{k≥2} 1/k² < 1 (key bound for squares case)
  - odd_count_lower_bound: count of odds in {0,...,n} is at least n/2
  - counterexample_positive_density: odd numbers ∪ {2m} has positive density ≥ 1/4
  - zero_sum_integer_form: clearing denominators in a rational zero-sum
  - NOT counterexample_fails_P1 (deep parity obstruction, beyond Aristotle)
  - NOT HasPropertyP1 results (main theorems backed by published papers)

  Mathematical context:
  ∑_{k≥2} 1/k² < 1 follows from ∑_{k≥2} 1/k² = π²/6 - 1 and π < 3.15,
  so π²/6 - 1 < 9.9225/6 - 1 ≈ 0.654 < 1.
  Density of the counterexample follows from odd numbers having density 1/2.
-/
import Mathlib

namespace Erdos318Aristotle

open Finset BigOperators Real

/- ## Definitions (mirrored from Erdos318Problem.lean) -/

/-- Signed sum of unit fractions. -/
def signedUnitSum (S : Finset ℕ) (f : ℕ → ℤ) : ℚ :=
  ∑ n ∈ S, (f n : ℚ) / (n : ℚ)

/-- A set A ⊆ ℕ has positive density if lim inf |A ∩ [0,n]| / n > 0. -/
def hasPositiveDensity (A : Set ℕ) : Prop :=
  ∃ δ : ℝ, δ > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
    (Finset.filter (· ∈ A) (Finset.range (n + 1))).card ≥ δ * n

/-- Counterexample: odd numbers plus one even number. -/
def counterexampleSet (m : ℕ) : Set ℕ :=
  {n : ℕ | n % 2 = 1 ∨ n = 2 * m}

/- ## Supporting Lemmas -/

/-- The count of odd numbers in {0, 1, ..., n} equals ⌊(n+1)/2⌋, so count * 2 ≥ n.
    Proved by induction: range(k+1) = insert k (range k), and if k is odd the
    filter gains one element (card increases by 1), otherwise card stays the same.
    In both cases omega closes the inductive step using count = k/2. -/
lemma odd_count_lower_bound (n : ℕ) :
    (Finset.filter (fun k => k % 2 = 1) (Finset.range (n + 1))).card * 2 ≥ n := by
  -- The count of odds in range(m) equals m/2 (Nat floor division)
  have key : ∀ m : ℕ, ((Finset.range m).filter (fun k => k % 2 = 1)).card = m / 2 := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.range_succ, Finset.filter_insert]
      split_ifs with hmod
      · -- k is odd: insert k, k ∉ range k so card increases by 1
        rw [Finset.card_insert_of_not_mem (by simp [Finset.mem_filter, Finset.mem_range])]
        omega
      · -- k is even: no change to filter, card unchanged
        omega
  -- count(range(n+1)) = (n+1)/2, and (n+1)/2 * 2 ≥ n by omega
  have h := key (n + 1)
  omega

/-- Pointwise bound: 1/k² ≤ 1/(k*(k-1)) for k ≥ 2, since k*(k-1) ≤ k². -/
lemma one_div_sq_le_one_div_mul_pred (k : ℕ) (hk : k ≥ 2) :
    (1 : ℝ) / (k : ℝ)^2 ≤ 1 / ((k : ℝ) * ((k : ℝ) - 1)) := by
  have hk' : (k : ℝ) ≥ 2 := by exact_mod_cast hk
  have hk1 : (k : ℝ) - 1 > 0 := by linarith
  have hkpos : (k : ℝ) > 0 := by linarith
  have hprod_pos : (k : ℝ) * ((k : ℝ) - 1) > 0 := mul_pos hkpos hk1
  -- k*(k-1) ≤ k², so 1/k² ≤ 1/(k*(k-1))
  apply one_div_le_one_div_of_le hprod_pos
  nlinarith

/-- ∑_{k≥2} 1/k² < 1.
    Proof: the sum equals π²/6 - 1 (using Basel/zeta(2)), and π < 3.15 gives
    π²/6 - 1 < 9.9225/6 - 1 ≈ 0.654 < 1. -/
theorem sum_reciprocal_squares_less_than_one :
    ∑' (k : ℕ), (if k ≥ 2 then (1 : ℝ) / k^2 else 0) < 1 := by
  -- The full Basel sum: ∑' n, 1/n² = π²/6
  have h_full_sum : ∑' n : ℕ, (1 : ℝ) / n^2 = Real.pi^2 / 6 := hasSum_zeta_two.tsum_eq
  -- The k<2 part has HasSum with sum = 1 (n=0 gives 0, n=1 gives 1)
  have h_lt2_hassum : HasSum (fun n : ℕ => if n < 2 then (1 : ℝ) / n^2 else 0) 1 := by
    -- Rewrite: if n < 2 then 1/n² else 0 = if n = 1 then 1 else 0
    have heq : (fun n : ℕ => if n < 2 then (1 : ℝ) / n^2 else 0) = fun n => if n = 1 then 1 else 0 := by
      ext n; rcases n with _ | _ | n
      · norm_num
      · norm_num
      · simp [show ¬(n + 2 < 2) from by omega, show ¬(n + 2 = 1) from by omega]
    rw [heq]
    exact hasSum_single 1 (fun b hb => if_neg hb)
  -- Summability of each piece
  have h_summ_ge2 : Summable (fun n : ℕ => if n ≥ 2 then (1 : ℝ) / n^2 else 0) :=
    Summable.of_nonneg_of_le
      (fun n => by split_ifs <;> norm_num)
      (fun n => by split_ifs <;> [exact le_refl _; exact div_nonneg one_pos.le (sq_nonneg _)])
      hasSum_zeta_two.summable
  have h_summ_lt2 := h_lt2_hassum.summable
  -- Decompose: 1/n² = (k≥2 part) + (k<2 part)
  have h_split : ∀ n : ℕ, (1 : ℝ) / n^2 =
      (if n ≥ 2 then (1 : ℝ) / n^2 else 0) + (if n < 2 then (1 : ℝ) / n^2 else 0) := by
    intro n
    by_cases h : n ≥ 2
    · simp [h, show ¬(n < 2) from by omega]
    · simp [h, show n < 2 from by omega]
  -- Add the two tsum pieces to get the full sum
  have h_add := tsum_add h_summ_ge2 h_summ_lt2
  simp_rw [← h_split] at h_add
  -- The k≥2 sum = π²/6 - 1
  have h_val : ∑' n : ℕ, (if n ≥ 2 then (1 : ℝ) / n^2 else 0) = Real.pi^2 / 6 - 1 := by
    have hlt2 := h_lt2_hassum.tsum_eq  -- ∑'(k<2) = 1
    linarith [h_add.trans h_full_sum, hlt2]  -- A + B = π²/6 and B = 1 → A = π²/6 - 1
  -- Conclude: π²/6 - 1 < 1 since π < 3.15
  rw [h_val]
  have hpi := Real.pi_lt_315
  nlinarith [Real.pi_pos]

/-- The counterexample set (odd numbers ∪ {2m}) has positive density ≥ 1/4.
    Since at least half of naturals are odd, the filter count ≥ (n+1)/2 ≥ n/4. -/
theorem counterexample_positive_density (m : ℕ) (hm : m ≥ 1) :
    hasPositiveDensity (counterexampleSet m) := by
  -- Use density δ = 1/4 and threshold N = 2
  refine ⟨1/4, by norm_num, 2, fun n hn => ?_⟩
  -- All odd numbers are in counterexampleSet m (via the left disjunct)
  have h_sub : (Finset.range (n + 1)).filter (fun k => k % 2 = 1) ⊆
               (Finset.range (n + 1)).filter (· ∈ counterexampleSet m) := by
    intro k hk
    simp only [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, Or.inl hk.2⟩
  -- Card of odds ≤ card of counterexampleSet filter
  have h_card : (Finset.filter (fun k => k % 2 = 1) (Finset.range (n + 1))).card ≤
                (Finset.filter (· ∈ counterexampleSet m) (Finset.range (n + 1))).card :=
    Finset.card_le_card h_sub
  -- Count of odds in range(n+1) = (n+1)/2 (by the key induction)
  have h_odd_count : (Finset.filter (fun k => k % 2 = 1) (Finset.range (n + 1))).card =
                     (n + 1) / 2 := by
    have key : ∀ k : ℕ, ((Finset.range k).filter (fun j => j % 2 = 1)).card = k / 2 := by
      intro k
      induction k with
      | zero => simp
      | succ j ihj =>
        rw [Finset.range_succ, Finset.filter_insert]
        split_ifs with hmod
        · rw [Finset.card_insert_of_not_mem (by simp [Finset.mem_filter, Finset.mem_range])]
          omega
        · omega
    exact key (n + 1)
  -- (n+1)/2 * 4 ≥ n (by Nat division: (n+1)/2 ≥ n/2 ≥ n/4)
  have h_nat : (n + 1) / 2 * 4 ≥ n := by omega
  -- Cast to ℝ: ((n+1)/2 : ℕ) ≥ 1/4 * n
  have h_real : ((n + 1) / 2 : ℕ) : ℝ ≥ 1 / 4 * n := by
    have h : (n : ℝ) ≤ 4 * (((n + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast h_nat
    linarith
  -- Combine: filter card ≥ (n+1)/2 ≥ 1/4 * n
  calc ((Finset.filter (· ∈ counterexampleSet m) (Finset.range (n + 1))).card : ℝ)
      ≥ ((Finset.filter (fun k => k % 2 = 1) (Finset.range (n + 1))).card : ℝ) := by
          exact_mod_cast h_card
    _ = ((n + 1) / 2 : ℕ) := by exact_mod_cast h_odd_count
    _ ≥ 1 / 4 * n := h_real

/-- Clearing denominators: if ∑_{n ∈ S} f(n)/n = 0 as rationals, then
    ∑_{n ∈ S} f(n) * (∏_{m ∈ S} m) / n = 0 as integers.
    Key: each n ∈ S divides ∏_{m ∈ S} m, making integer division exact.

    Proof outline:
    1. For each n ∈ S: f(n)*P/n = f(n)*(P/n) since n | P (Int.mul_ediv_assoc)
    2. Sum: ∑ f(n)*(P/n) where P/n = ∏_{m ∈ S\{n}} m
    3. Cast to ℚ using exactness of division, then use signedUnitSum = 0
    Steps 2-3 require careful type management between ℤ and ℚ divisions. -/
theorem zero_sum_integer_form (S : Finset ℕ) (f : ℕ → ℤ) (hS : S.Nonempty)
    (h0 : ∀ n ∈ S, n ≠ 0) (hzero : signedUnitSum S f = 0) :
    ∑ n ∈ S, f n * (∏ m ∈ S, m) / n = 0 := by
  -- Each n ∈ S divides ∏ m ∈ S, m (as integers)
  have h_dvd_nat : ∀ n ∈ S, n ∣ ∏ m ∈ S, m := fun n hn => Finset.dvd_prod_of_mem _ hn
  -- Rewrite: f n * P / n = f n * (P / n) since n | P (exact integer division)
  have h_exact : ∀ n ∈ S, f n * ↑(∏ m ∈ S, m) / (n : ℤ) = f n * (↑(∏ m ∈ S, m) / (n : ℤ)) := by
    intro n hn
    have hdvd : (n : ℤ) ∣ ↑(∏ m ∈ S, m) := by exact_mod_cast h_dvd_nat n hn
    rw [Int.mul_ediv_assoc _ hdvd]
  simp_rw [Finset.sum_congr rfl h_exact]
  -- Now prove ∑ n ∈ S, f n * (P / n : ℤ) = 0
  -- via casting to ℚ: the ℤ/n is exact, matching the ℚ structure
  apply_fun (Int.cast : ℤ → ℚ) using Int.cast_injective
  push_cast
  simp only [Int.cast_sum, Int.cast_mul]
  -- Rearrange to match signedUnitSum
  conv_lhs =>
    arg 2; ext n
    rw [show (f n : ℚ) * (↑(∏ m ∈ S, m) / ↑n) =
             ((f n : ℚ) / ↑n) * ↑(∏ m ∈ S, m) from by ring]
  rw [← Finset.sum_mul]
  have hsu : ∑ n ∈ S, (f n : ℚ) / ↑n = 0 := by
    have : signedUnitSum S f = ∑ n ∈ S, (f n : ℚ) / ↑n := rfl
    rw [← this]; exact hzero
  rw [hsu, zero_mul]

end Erdos318Aristotle
