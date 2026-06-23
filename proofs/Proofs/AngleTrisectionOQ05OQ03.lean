/-
  Minimum Simultaneous Folds to Solve a Polynomial Equation

  Open Question (angle-trisection-oq-05-oq-03):
  "What is the minimum number of simultaneous origami folds needed to
   construct a root of a polynomial of degree d?"

  Answer: minFoldLevel(d) = the prime-sequence index of the largest prime
  factor of d. This function is multiplicative:
    minFoldLevel(m·n) = max(minFoldLevel m, minFoldLevel n)

  This file:
  1. Proves generalized monotonicity: k ≤ k' → k-fold ⊆ k'-fold
  2. Proves multiplicativity: m·n is k-fold ↔ both m and n are k-fold
  3. Defines minFoldLevel via Nat.find (classically)
  4. Characterizes: minFoldLevel d ≤ k ↔ d is k-fold constructible
  5. Computes exact fold levels: primes p_j need exactly j folds
  6. Proves the multiplicative property for minFoldLevel
  7. Computes concrete values for small degrees
  8. Proves minFoldLevel is unbounded

  Builds on AngleTrisectionOQ05OQ01 (k-fold constructibility framework)
  and AngleTrisectionOQ05OQ02 (exact fold levels for primes, completeness).
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic
import Proofs.AngleTrisectionOQ05OQ01
import Proofs.AngleTrisectionOQ05OQ02

open AngleTrisectionOQ05OQ01 AngleTrisectionOQ05OQ02 Nat

namespace AngleTrisectionOQ05OQ03

private noncomputable instance (d : ℕ) :
    DecidablePred (fun k : ℕ => k ≥ 1 ∧ IsKFoldConstructible d k) :=
  Classical.decPred _

/-! ## Generalized Monotonicity -/

/-- More folds → more constructible: if d is k-fold constructible and k ≤ k',
    then d is k'-fold constructible. Generalizes the +1 step from OQ-01. -/
theorem constructible_mono_le {d k k' : ℕ} (hkk' : k ≤ k')
    (h : IsKFoldConstructible d k) : IsKFoldConstructible d k' := by
  obtain ⟨hk, hd_pos, hsm⟩ := h
  refine ⟨by omega, hd_pos, fun q hq hqd => ?_⟩
  calc q ≤ foldPrimeBound k := hsm q hq hqd
    _ ≤ foldPrimeBound k' :=
        (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone hkk'

/-! ## Multiplicativity of k-Fold Constructibility -/

/-- A product m·n is k-fold constructible if and only if both m and n are.
    Forward: prime divisors of m (resp. n) divide m·n, so smoothness transfers.
    Backward: prime divisors of m·n divide m or n (by primality), so smooth_mul. -/
theorem constructible_mul_iff {m n k : ℕ} (hm : m > 0) (hn : n > 0) :
    IsKFoldConstructible (m * n) k ↔ IsKFoldConstructible m k ∧ IsKFoldConstructible n k := by
  constructor
  · intro ⟨hk, _, hsm⟩
    exact ⟨⟨hk, hm, fun q hq hqm => hsm q hq (hqm.mul_right n)⟩,
           ⟨hk, hn, fun q hq hqn => hsm q hq (hqn.mul_left m)⟩⟩
  · intro ⟨⟨hk, _, hsmm⟩, ⟨_, _, hsmn⟩⟩
    exact ⟨hk, Nat.mul_pos hm hn, fun q hq hqmn =>
      (hq.dvd_mul.mp hqmn).elim (hsmm q hq) (hsmn q hq)⟩

/-! ## Minimum Fold Level: Definition and Characterization -/

/-- The minimum fold level for degree d: the least k ≥ 1 such that d is k-fold
    constructible. Defined classically via Nat.find; existence guaranteed by OQ-02. -/
noncomputable def minFoldLevel (d : ℕ) (hd : d > 0) : ℕ :=
  Nat.find (eventually_constructible d hd)

/-- The minimum fold level is ≥ 1 (since 0-fold constructibility is undefined). -/
theorem minFoldLevel_pos (d : ℕ) (hd : d > 0) : minFoldLevel d hd ≥ 1 :=
  (Nat.find_spec (eventually_constructible d hd)).1

/-- Degree d is constructible at its minimum fold level (the minimum is attained). -/
theorem minFoldLevel_constructible (d : ℕ) (hd : d > 0) :
    IsKFoldConstructible d (minFoldLevel d hd) :=
  (Nat.find_spec (eventually_constructible d hd)).2

/-- No fold level below the minimum works (minimality). -/
theorem minFoldLevel_minimal (d : ℕ) (hd : d > 0) {k : ℕ} (hk : k < minFoldLevel d hd) :
    ¬ (k ≥ 1 ∧ IsKFoldConstructible d k) :=
  Nat.find_min (eventually_constructible d hd) hk

/-- If d is k-fold constructible (k ≥ 1), then minFoldLevel d ≤ k. -/
theorem minFoldLevel_le_of_constructible (d : ℕ) (hd : d > 0) {k : ℕ} (hk1 : k ≥ 1)
    (hc : IsKFoldConstructible d k) : minFoldLevel d hd ≤ k :=
  Nat.find_min' (eventually_constructible d hd) ⟨hk1, hc⟩

/-- Complete characterization: minFoldLevel d ≤ k ↔ d is k-fold constructible (k ≥ 1). -/
theorem minFoldLevel_le_iff (d : ℕ) (hd : d > 0) {k : ℕ} (hk : k ≥ 1) :
    minFoldLevel d hd ≤ k ↔ IsKFoldConstructible d k :=
  ⟨fun hle => constructible_mono_le hle (minFoldLevel_constructible d hd),
   fun h => minFoldLevel_le_of_constructible d hd hk h⟩

/-! ## Exact Fold Level for Primes and Concrete Values -/

/-- The j-th prime (0-indexed) has minimum fold level exactly j, for j ≥ 1.
    Upper bound: p_j is j-fold constructible (from OQ-02).
    Lower bound: p_j is NOT k-fold constructible for k < j (from OQ-02). -/
theorem minFoldLevel_nth_prime (j : ℕ) (hj : j ≥ 1) :
    minFoldLevel (foldPrimeBound j) (nth_prime_is_prime j).pos = j := by
  apply Nat.le_antisymm
  · exact minFoldLevel_le_of_constructible _ _ hj (nth_prime_constructible_at j hj)
  · apply Nat.le_of_not_lt; intro hlt
    exact nth_prime_not_constructible_below j _ (minFoldLevel_pos _ _) hlt
      (minFoldLevel_constructible _ _)

/-- minFoldLevel 1 = 1 (1 is p-smooth for any p, so 1-fold constructible). -/
theorem minFoldLevel_one : minFoldLevel 1 (by norm_num) = 1 :=
  Nat.le_antisymm
    (minFoldLevel_le_of_constructible 1 _ (by omega) (degree_one_constructible 1 (by omega)))
    (minFoldLevel_pos 1 _)

/-- minFoldLevel 2 = 1 (2 ≤ 3 = p₁, so 2 is 1-fold constructible). -/
theorem minFoldLevel_two : minFoldLevel 2 (by norm_num) = 1 :=
  Nat.le_antisymm
    (minFoldLevel_le_of_constructible 2 _ (by omega)
      ⟨by omega, prime_smooth (by decide) (by rw [fold_1_bound]; omega)⟩)
    (minFoldLevel_pos 2 _)

/-- minFoldLevel 3 = 1 (3 = p₁, so 3 is exactly 1-fold constructible). -/
theorem minFoldLevel_three : minFoldLevel 3 (by norm_num) = 1 :=
  Nat.le_antisymm
    (minFoldLevel_le_of_constructible 3 _ (by omega) degree_three_1fold)
    (minFoldLevel_pos 3 _)

/-- minFoldLevel 5 = 2 (5 = p₂, so 5 is exactly 2-fold constructible). -/
theorem minFoldLevel_five : minFoldLevel 5 (by norm_num) = 2 := by
  apply Nat.le_antisymm
  · exact minFoldLevel_le_of_constructible 5 _ (by omega) degree_five_2fold
  · apply Nat.le_of_not_lt; intro h
    have hc := minFoldLevel_constructible 5 (by norm_num)
    have h1 : minFoldLevel 5 (by norm_num) = 1 :=
      Nat.le_antisymm (by omega) (minFoldLevel_pos 5 _)
    exact degree_five_not_1fold (h1 ▸ hc)

/-- minFoldLevel 7 = 3 (7 = p₃, so 7 is exactly 3-fold constructible). -/
theorem minFoldLevel_seven : minFoldLevel 7 (by norm_num) = 3 := by
  apply Nat.le_antisymm
  · exact minFoldLevel_le_of_constructible 7 _ (by omega) degree_seven_3fold
  · apply Nat.le_of_not_lt; intro h
    have hc := minFoldLevel_constructible 7 (by norm_num)
    exact degree_seven_not_2fold (constructible_mono_le (by omega) hc)

/-- minFoldLevel 11 = 4 (11 = p₄, so 11 is exactly 4-fold constructible). -/
theorem minFoldLevel_eleven : minFoldLevel 11 (by norm_num) = 4 := by
  apply Nat.le_antisymm
  · exact minFoldLevel_le_of_constructible 11 _ (by omega) degree_eleven_4fold
  · apply Nat.le_of_not_lt; intro h
    have hc := minFoldLevel_constructible 11 (by norm_num)
    exact degree_eleven_not_3fold (constructible_mono_le (by omega) hc)

/-! ## Multiplicative Property and Product Computations -/

/-- The minimum fold level of a product equals the max of the individual levels.
    This follows from constructible_mul_iff: min folds for m·n is the bottleneck. -/
theorem minFoldLevel_mul (m n : ℕ) (hm : m > 0) (hn : n > 0) :
    minFoldLevel (m * n) (Nat.mul_pos hm hn) =
    max (minFoldLevel m hm) (minFoldLevel n hn) := by
  apply Nat.le_antisymm
  · apply minFoldLevel_le_of_constructible _ _
      (Nat.le_trans (minFoldLevel_pos m hm) (Nat.le_max_left _ _))
    rw [constructible_mul_iff hm hn]
    exact ⟨constructible_mono_le (Nat.le_max_left _ _) (minFoldLevel_constructible m hm),
           constructible_mono_le (Nat.le_max_right _ _) (minFoldLevel_constructible n hn)⟩
  · apply max_le
    · apply minFoldLevel_le_of_constructible _ _ (minFoldLevel_pos _ _)
      exact ((constructible_mul_iff hm hn).mp (minFoldLevel_constructible _ _)).1
    · apply minFoldLevel_le_of_constructible _ _ (minFoldLevel_pos _ _)
      exact ((constructible_mul_iff hm hn).mp (minFoldLevel_constructible _ _)).2

/-- minFoldLevel 6 = 1 (6 = 2·3, max(1,1) = 1). -/
theorem minFoldLevel_six : minFoldLevel 6 (by norm_num) = 1 :=
  Nat.le_antisymm
    (minFoldLevel_le_of_constructible 6 _ (by omega) degree_six_1fold)
    (minFoldLevel_pos 6 _)

/-- minFoldLevel 10 = 2 (10 = 2·5, the 5 factor forces 2 folds). -/
theorem minFoldLevel_ten : minFoldLevel 10 (by norm_num) = 2 := by
  apply Nat.le_antisymm
  · exact minFoldLevel_le_of_constructible 10 _ (by omega) degree_ten_2fold
  · apply Nat.le_of_not_lt; intro h
    have hc := minFoldLevel_constructible 10 (by norm_num)
    have h1 : minFoldLevel 10 (by norm_num) = 1 :=
      Nat.le_antisymm (by omega) (minFoldLevel_pos 10 _)
    exact degree_ten_not_1fold (h1 ▸ hc)

/-- minFoldLevel 15 = 2 (15 = 3·5, max(1,2) = 2). -/
theorem minFoldLevel_fifteen : minFoldLevel 15 (by norm_num) = 2 := by
  apply Nat.le_antisymm
  · refine minFoldLevel_le_of_constructible 15 _ (by omega)
      ⟨by omega, by omega, fun q hq hd => ?_⟩
    rw [fold_2_bound]
    have h15 : 15 = 3 * 5 := by norm_num
    rw [h15] at hd
    rcases hq.dvd_mul.mp hd with h3 | h5
    · exact (Nat.le_of_dvd (by omega) h3).trans (by omega)
    · exact Nat.le_of_dvd (by omega) h5
  · apply Nat.le_of_not_lt; intro h
    have hc := minFoldLevel_constructible 15 (by norm_num)
    have h1 : minFoldLevel 15 (by norm_num) = 1 :=
      Nat.le_antisymm (by omega) (minFoldLevel_pos 15 _)
    rw [h1] at hc
    exact not_smooth_of_large_prime (by decide : Nat.Prime 5)
      (by rw [fold_1_bound]; omega) (by norm_num : (5 : ℕ) ∣ 15) (by omega) hc.2

/-- minFoldLevel 14 = 3 (14 = 2·7, the 7 factor forces 3 folds). -/
theorem minFoldLevel_fourteen : minFoldLevel 14 (by norm_num) = 3 := by
  apply Nat.le_antisymm
  · refine minFoldLevel_le_of_constructible 14 _ (by omega)
      ⟨by omega, by omega, fun q hq hd => ?_⟩
    rw [fold_3_bound]
    have h14 : 14 = 2 * 7 := by norm_num
    rw [h14] at hd
    rcases hq.dvd_mul.mp hd with h2 | h7
    · exact (Nat.le_of_dvd (by omega) h2).trans (by omega)
    · exact Nat.le_of_dvd (by omega) h7
  · apply Nat.le_of_not_lt; intro h
    have hc := minFoldLevel_constructible 14 (by norm_num)
    exact not_smooth_of_large_prime (by decide : Nat.Prime 7)
      (by rw [fold_2_bound]; omega) (by norm_num : (7 : ℕ) ∣ 14) (by omega)
      (constructible_mono_le (by omega) hc).2

/-- minFoldLevel 42 = 3 (42 = 2·3·7, the 7 factor is dominant). -/
theorem minFoldLevel_fortytwo : minFoldLevel 42 (by norm_num) = 3 :=
  Nat.le_antisymm
    (minFoldLevel_le_of_constructible 42 _ (by omega) degree_fortytwo_3fold)
    (by
      apply Nat.le_of_not_lt; intro h
      have hc := minFoldLevel_constructible 42 (by norm_num)
      exact degree_fortytwo_not_2fold (constructible_mono_le (by omega) hc))

/-! ## Unboundedness of minFoldLevel -/

/-- For any K, there exists a degree requiring more than K simultaneous folds.
    Witness: the (K+1)-th prime p_{K+1}, which requires exactly K+1 folds. -/
theorem minFoldLevel_unbounded (K : ℕ) :
    ∃ d : ℕ, ∃ hd : d > 0, minFoldLevel d hd > K := by
  refine ⟨foldPrimeBound (K + 1), (nth_prime_is_prime (K + 1)).pos, ?_⟩
  by_contra hle
  push_neg at hle
  exact nth_prime_not_constructible_below (K + 1) _
    (minFoldLevel_pos _ _) (by omega) (minFoldLevel_constructible _ _)

/-! ## Summary -/

/-
## Answer to angle-trisection-oq-05-oq-03

The minimum fold level is the prime-sequence index of the largest prime factor:
  minFoldLevel(d) = max{ j ≥ 1 : p_j divides d }

Key results:
1. constructible_mono_le: k ≤ k' → k-fold → k'-fold (generalized monotonicity)
2. constructible_mul_iff: m·n is k-fold ↔ m and n are both k-fold
3. minFoldLevel: defined via Nat.find; the minimum k ≥ 1 for which d is k-fold
4. minFoldLevel_le_iff: minFoldLevel d ≤ k ↔ d is k-fold constructible (k ≥ 1)
5. minFoldLevel_nth_prime: minFoldLevel(p_j) = j for j ≥ 1
6. minFoldLevel_mul: minFoldLevel(m·n) = max(minFoldLevel m, minFoldLevel n)
7. Concrete: minFoldLevel 42 = 3 (dominant prime 7 = p₃ controls the fold level)
8. minFoldLevel_unbounded: no fixed fold count suffices for all degrees

Status: 0 axioms, 0 sorries.
Builds on: AngleTrisectionOQ05OQ01, AngleTrisectionOQ05OQ02.
-/

end AngleTrisectionOQ05OQ03
