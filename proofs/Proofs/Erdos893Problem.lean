/-
Erdős Problem #893: Divisor Sum of Mersenne Numbers

Source: https://erdosproblems.com/893
Status: OPEN (partially resolved by Kovač-Luca 2025)

Statement:
Define f(n) = Σ_{k=1}^n τ(2^k - 1), where τ is the divisor counting function.
Does f(2n)/f(n) tend to a limit?

Known Results:
- Kovač-Luca (2025): limsup f(2n)/f(n) = ∞, ruling out any finite limit
- Numerical evidence suggests lim f(2n)/f(n) = ∞
- Erdős noted f(n) likely has no simple asymptotic formula

References: [Er98], [KoLu25] arXiv:2506.04883

Adapted from erdosproblems.com (Apache 2.0 License)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Finset

namespace Erdos893

/-
## Part I: Divisor Counting Function
-/

/-- The number of divisors of n. -/
def tau (n : ℕ) : ℕ := n.divisors.card

/-
## Part II: Verified Small Values of τ

We verify τ for small Mersenne numbers 2^k - 1.
-/

-- τ(1) = 1 (2^1 - 1 = 1, divisors: {1})
theorem tau_1 : tau 1 = 1 := by native_decide

-- τ(3) = 2 (2^2 - 1 = 3, divisors: {1, 3})
theorem tau_3 : tau 3 = 2 := by native_decide

-- τ(7) = 2 (2^3 - 1 = 7, divisors: {1, 7})
theorem tau_7 : tau 7 = 2 := by native_decide

-- τ(15) = 4 (2^4 - 1 = 15 = 3·5, divisors: {1, 3, 5, 15})
theorem tau_15 : tau 15 = 4 := by native_decide

-- τ(31) = 2 (2^5 - 1 = 31, divisors: {1, 31})
theorem tau_31 : tau 31 = 2 := by native_decide

-- τ(63) = 6 (2^6 - 1 = 63 = 7·9, divisors: {1, 3, 7, 9, 21, 63})
theorem tau_63 : tau 63 = 6 := by native_decide

-- τ(127) = 2 (2^7 - 1 = 127, Mersenne prime)
theorem tau_127 : tau 127 = 2 := by native_decide

-- τ(255) = 8 (2^8 - 1 = 255 = 3·5·17)
theorem tau_255 : tau 255 = 8 := by native_decide

/-- Mersenne primes have exactly 2 divisors. -/
theorem tau_prime_eq_two {p : ℕ} (hp : Nat.Prime p) : tau p = 2 := by
  simp [tau, Nat.Prime.divisors hp]

/-- τ(n) > 0 for n ≥ 1: every positive number has at least one divisor. -/
theorem tau_pos {n : ℕ} (hn : 0 < n) : 0 < tau n :=
  Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd n, by omega⟩⟩

/-- For n ≥ 2, τ(n) ≥ 2: 1 and n are distinct divisors. -/
theorem tau_ge_two {n : ℕ} (hn : 2 ≤ n) : 2 ≤ tau n := by
  simp only [tau]
  have h1 : 1 ∈ n.divisors := Nat.mem_divisors.mpr ⟨one_dvd n, by omega⟩
  have hn_mem : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_refl n, by omega⟩
  have : 1 < n.divisors.card := by
    rw [Finset.one_lt_card]
    exact ⟨1, h1, n, hn_mem, by omega⟩
  omega

/-
## Part III: The Cumulative Sum f(n)
-/

/-- f(n) = Σ_{k=1}^n τ(2^k - 1), the cumulative divisor count
    of Mersenne numbers. -/
def f (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, tau (2 ^ k - 1)

-- f(1) = τ(1) = 1
theorem f_one : f 1 = 1 := by native_decide

-- f(2) = τ(1) + τ(3) = 1 + 2 = 3
theorem f_two : f 2 = 3 := by native_decide

-- f(3) = τ(1) + τ(3) + τ(7) = 1 + 2 + 2 = 5
theorem f_three : f 3 = 5 := by native_decide

-- f(4) = 5 + τ(15) = 5 + 4 = 9
theorem f_four : f 4 = 9 := by native_decide

-- f(5) = 9 + τ(31) = 9 + 2 = 11
theorem f_five : f 5 = 11 := by native_decide

-- f(6) = 11 + τ(63) = 11 + 6 = 17
theorem f_six : f 6 = 17 := by native_decide

-- f(7) = 17 + τ(127) = 17 + 2 = 19
theorem f_seven : f 7 = 19 := by native_decide

-- f(8) = 19 + τ(255) = 19 + 8 = 27
theorem f_eight : f 8 = 27 := by native_decide

/-- Collected verified values of f. -/
theorem f_initial_values :
    f 1 = 1 ∧ f 2 = 3 ∧ f 3 = 5 ∧ f 4 = 9 ∧
    f 5 = 11 ∧ f 6 = 17 ∧ f 7 = 19 ∧ f 8 = 27 :=
  ⟨f_one, f_two, f_three, f_four, f_five, f_six, f_seven, f_eight⟩

/-- Recurrence: f(n+1) = f(n) + τ(2^(n+1) - 1). -/
theorem f_succ (n : ℕ) : f (n + 1) = f n + tau (2 ^ (n + 1) - 1) := by
  unfold f
  have h : Finset.Icc 1 (n + 1) = Finset.Icc 1 n ∪ {n + 1} := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]; omega
  have hdisj : Disjoint (Finset.Icc 1 n) {n + 1} := by
    simp only [Finset.disjoint_singleton_right, Finset.mem_Icc, not_and, not_le]; intro; omega
  rw [h, Finset.sum_union hdisj, Finset.sum_singleton]

/-
## Part IV: Monotonicity
-/

/-- f is monotone: adding more terms only increases the sum. -/
theorem f_mono {m n : ℕ} (h : m ≤ n) : f m ≤ f n := by
  simp only [f]
  apply Finset.sum_le_sum_of_subset
  exact Finset.Icc_subset_Icc_right h

/-- f is strictly positive for n ≥ 1. -/
theorem f_pos {n : ℕ} (hn : 1 ≤ n) : 0 < f n := by
  calc 0 < f 1 := by rw [f_one]; omega
    _ ≤ f n := f_mono hn

/-- f(n) ≥ n for all n: each term τ(2^k - 1) ≥ 1. -/
theorem f_ge (n : ℕ) : n ≤ f n := by
  unfold f
  calc n = (Finset.Icc 1 n).card := by simp [Finset.card_Icc]; omega
    _ = ∑ _ ∈ Finset.Icc 1 n, 1 := by rw [Finset.sum_const]; simp
    _ ≤ ∑ k ∈ Finset.Icc 1 n, tau (2 ^ k - 1) := by
        apply Finset.sum_le_sum; intro k hk
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        have : 2 ≤ 2 ^ k := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
        exact tau_pos (by omega)

/-- f(n) ≥ 2n - 1 for n ≥ 1: stronger bound using τ(2^k - 1) ≥ 2 for k ≥ 2. -/
theorem f_lower_bound {n : ℕ} (hn : 1 ≤ n) : 2 * n - 1 ≤ f n := by
  induction n with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => have := f_one; omega
    | succ k =>
      have hf := f_succ (k + 1)
      have ih' : 2 * (k + 1) - 1 ≤ f (k + 1) := ih (by omega)
      have hpow : 4 ≤ 2 ^ (k + 2) := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have htau : 2 ≤ tau (2 ^ (k + 2) - 1) := tau_ge_two (by omega)
      omega

/-- f(2n) splits into f(n) plus the contribution from k ∈ [n+1, 2n]. -/
theorem f_decomp (n : ℕ) :
    f (2 * n) = f n + ∑ k ∈ Finset.Icc (n + 1) (2 * n), tau (2 ^ k - 1) := by
  simp only [f]
  have hsplit : Finset.Icc 1 (2 * n) = Finset.Icc 1 n ∪ Finset.Icc (n + 1) (2 * n) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 1 n) (Finset.Icc (n + 1) (2 * n)) := by
    simp only [Finset.disjoint_left, Finset.mem_Icc]
    intro x ⟨_, hx⟩ ⟨hx', _⟩; omega
  rw [hsplit, Finset.sum_union hdisj]

/-- The extra terms in f(2n) beyond f(n) sum to at least 2n (for n ≥ 1). -/
theorem f_gap_lower_bound {n : ℕ} (hn : 1 ≤ n) :
    2 * n ≤ ∑ k ∈ Finset.Icc (n + 1) (2 * n), tau (2 ^ k - 1) := by
  have hcard : (Finset.Icc (n + 1) (2 * n)).card = n := by
    rw [Finset.card_Icc]; omega
  calc 2 * n
      = ∑ _ ∈ Finset.Icc (n + 1) (2 * n), 2 := by
        rw [Finset.sum_const, hcard, smul_eq_mul]; ring
    _ ≤ ∑ k ∈ Finset.Icc (n + 1) (2 * n), tau (2 ^ k - 1) := by
        apply Finset.sum_le_sum
        intro k hk
        simp only [Finset.mem_Icc] at hk
        apply tau_ge_two
        have : 4 ≤ 2 ^ k := by
          calc (4 : ℕ) = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega

/-
## Part IV-b: Mersenne Divisibility and Tau Bounds

Key structural property: divisors of k inject into divisors of 2^k - 1
via d ↦ 2^d - 1, giving τ(2^k - 1) ≥ τ(k). This connects the growth
of f to the divisor summatory function Σ τ(k).
-/

/-- If a ∣ b then (2^a - 1) ∣ (2^b - 1). Mersenne divisibility. -/
theorem mersenne_dvd {a b : ℕ} (h : a ∣ b) : (2 ^ a - 1) ∣ (2 ^ b - 1) := by
  obtain ⟨m, rfl⟩ := h
  induction m with
  | zero => simp
  | succ m ih =>
    rw [mul_succ, pow_add]
    have h2a : 1 ≤ 2 ^ a := Nat.one_le_pow _ 2 (by norm_num)
    have h2am : 1 ≤ 2 ^ (a * m) := Nat.one_le_pow _ 2 (by norm_num)
    have h_prod : 1 ≤ 2 ^ (a * m) * 2 ^ a := by rw [← pow_add]; exact Nat.one_le_pow _ 2 (by norm_num)
    -- Identity: x*y - 1 = x*(y-1) + (x-1) for x,y �� 1
    have key : 2 ^ (a * m) * 2 ^ a - 1 =
        2 ^ (a * m) * (2 ^ a - 1) + (2 ^ (a * m) - 1) := by
      zify [h2a, h2am, h_prod]; ring
    rw [key]
    exact Nat.dvd_add (dvd_mul_left _ _) ih

/-- The map d ↦ 2^d - 1 is injective on positive naturals. -/
private theorem mersenne_injective {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : 2 ^ a - 1 = 2 ^ b - 1) : a = b := by
  have h2a : 1 ≤ 2 ^ a := Nat.one_le_pow _ 2 (by norm_num)
  have h2b : 1 ≤ 2 ^ b := Nat.one_le_pow _ 2 (by norm_num)
  have heq : 2 ^ a = 2 ^ b := by omega
  by_contra h_ne
  rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
  · exact absurd heq (Nat.pow_lt_pow_right (by norm_num : 1 < 2) h_lt).ne
  · exact absurd heq (Nat.pow_lt_pow_right (by norm_num : 1 < 2) h_gt).ne'

/-- τ(2^k - 1) ≥ τ(k): divisors of k inject into divisors of 2^k - 1
    via the map d ↦ 2^d - 1. -/
theorem tau_mersenne_ge_tau {k : ℕ} (hk : 1 ≤ k) : tau k ≤ tau (2 ^ k - 1) := by
  unfold tau
  apply Finset.card_le_card_of_injOn (fun d => 2 ^ d - 1)
  · -- The map sends k.divisors into (2^k - 1).divisors
    intro d hd
    rw [Nat.mem_divisors] at hd ⊢
    refine ⟨mersenne_dvd hd.1, ?_⟩
    have : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  · -- The map is injective on k.divisors
    intro a ha b hb hab
    rw [Finset.mem_coe, Nat.mem_divisors] at ha hb
    exact mersenne_injective (Nat.pos_of_dvd_of_pos ha.1 (by omega))
                              (Nat.pos_of_dvd_of_pos hb.1 (by omega)) hab

/-- f(n) ≥ Σ_{k=1}^n τ(k): the Mersenne tau bound applied term by term.
    Since Σ_{k=1}^n τ(k) ~ n log n (Dirichlet), this gives f(n) ≫ n log n. -/
theorem f_divisor_sum_lower (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, tau k ≤ f n := by
  unfold f
  apply Finset.sum_le_sum
  intro k hk
  exact tau_mersenne_ge_tau (Finset.mem_Icc.mp hk).1

/-
## Part V: The Ratio f(2n)/f(n)
-/

/-- The ratio f(2n)/f(n) as a real number. -/
noncomputable def ratio (n : ℕ) : ℝ :=
  (f (2 * n) : ℝ) / (f n : ℝ)

/-- The ratio is at least 1 for n ≥ 1 (since f(2n) ≥ f(n)). -/
theorem ratio_ge_one {n : ℕ} (hn : 1 ≤ n) : 1 ≤ ratio n := by
  simp only [ratio]
  rw [le_div_iff₀ (by exact_mod_cast f_pos hn)]
  simp
  exact_mod_cast f_mono (by omega : n ≤ 2 * n)

/-
## Part VI: Known Results
-/

/-- Kovač-Luca (2025): limsup f(2n)/f(n) = ∞.
    For every M > 0, there exists n with f(2n)/f(n) > M. -/
axiom kovac_luca_limsup_infinite :
  ∀ M : ℝ, M > 0 → ∃ n : ℕ, ratio n > M

/-- Consequence: the ratio is not bounded above. -/
theorem ratio_unbounded : ¬∃ B : ℝ, ∀ n : ℕ, ratio n ≤ B := by
  intro ⟨B, hB⟩
  obtain ⟨n, hn⟩ := kovac_luca_limsup_infinite (max B 1) (by positivity)
  have := hB n
  linarith [le_max_left B 1]

/-
## Part VII: The Main Question (Erdős Problem #893)
-/

/-- Erdős Problem #893 (OPEN): Does f(2n)/f(n) → ∞ as n → ∞?
    This is stronger than Kovač-Luca's limsup result. -/
def ErdosProblem893 : Prop :=
  ∀ M : ℝ, M > 0 →
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ratio n > M

/-- The Kovač-Luca result is weaker: it gives existence but not eventual. -/
theorem kovac_luca_weaker_than_conjecture :
    ErdosProblem893 → (∀ M : ℝ, M > 0 → ∃ n : ℕ, ratio n > M) := by
  intro h M hM
  obtain ⟨N₀, hN⟩ := h M hM
  exact ⟨N₀, hN N₀ (le_refl _)⟩

/-
## Part VIII: Summary
-/

/-- Summary of verified computations and known results. -/
theorem erdos893_summary :
    -- f is strictly positive and monotone
    (∀ n, 1 ≤ n → 0 < f n) ∧
    (∀ m n, m ≤ n → f m ≤ f n) ∧
    -- The ratio is unbounded (Kovač-Luca)
    (¬∃ B : ℝ, ∀ n : ℕ, ratio n ≤ B) :=
  ⟨fun n hn => f_pos hn, fun m n h => f_mono h, ratio_unbounded⟩

end Erdos893
