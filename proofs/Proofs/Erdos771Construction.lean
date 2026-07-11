/-
# Erdős Problem #771 — the Erdős–Graham construction, verified

Erdős #771 concerns `f(n)` = the largest `k` such that for every `m ≥ 1` there is an
`m`-avoiding set `S ⊆ {1,…,n}` with `|S| = k` (no nonempty subset of `S` sums to `m`).
The answer `f(n) = (1/2 + o(1)) · n / log n` is known (Erdős–Graham lower bound,
Alon–Freiman upper bound), and both bounds are deep.

This file does NOT reprove the asymptotics. It **fully verifies (0 axioms, 0 sorries)** the
elementary **construction** at the heart of the Erdős–Graham *lower* bound, which the
companion `Erdos771Problem.lean` left as `sorry` (and which, in any case, no longer compiles
under Mathlib 4.26.0 — stale module path, `DecidablePred` gaps, and dangling doc-comments;
flagged for a Mechanic). The construction is:

> Take `S = ` the multiples of a prime `p` in `{1,…,n}`. Every subset sum of `S` is a
> multiple of `p`, so if `p ∤ m` then `m` is **not** a subset sum — `S` avoids `m`.

We verify:
* `prime_multiples_size` — `|S| = ⌊n/p⌋` (the size of the construction).
* `prime_multiples_avoid` — if `p` is prime and `p ∤ m`, then `S` avoids `m`.
* `exists_prime_not_dvd` — for every `m ≥ 1` there is a prime `p ∤ m`.
* `exists_avoiding_multiples` — hence for every `m ≥ 1` the construction yields an
  `m`-avoiding subset of `{1,…,n}`. This is the existence statement the lower bound rests on.

## References
- Erdős, P., Graham, R. "Old and new problems and results in combinatorial number theory."
- Alon, N., Freiman, G. (upper bound).
- https://erdosproblems.com/771
-/

import Mathlib

open Finset

namespace Erdos771Construction

/-! ## Definitions (self-contained) -/

/-- The set `{1, …, n}`. -/
def Icc_n (n : ℕ) : Finset ℕ := Finset.Icc 1 n

/-- The set of positive subset sums of `S`. -/
noncomputable def subsetSums (S : Finset ℕ) : Finset ℕ :=
  (S.powerset.image (fun A => ∑ a ∈ A, a)).filter (· > 0)

/-- `S` avoids sum `m` if `m` is not a (positive) subset sum of `S`. -/
def AvoidSum (S : Finset ℕ) (m : ℕ) : Prop :=
  m ∉ subsetSums S

/-- The construction: the multiples of `p` inside `{1, …, n}`. -/
def primeMultiples (p n : ℕ) : Finset ℕ :=
  (Icc_n n).filter (fun k => p ∣ k)

/-! ## Size of the construction -/

/-- The number of multiples of `p` in `{1, …, n}` is `⌊n/p⌋`. -/
theorem prime_multiples_size (p n : ℕ) :
    (primeMultiples p n).card = n / p := by
  have hIcc : Icc_n n = Finset.Ioc 0 n := by
    unfold Icc_n; ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  unfold primeMultiples
  rw [hIcc]
  exact Nat.Ioc_filter_dvd_card_eq_div n p

/-! ## The avoidance property -/

/-- **Erdős–Graham construction.** If `p` is prime and `p ∤ m`, then the multiples of `p`
    in `{1, …, n}` avoid `m`: every subset sum is divisible by `p`, but `m` is not. -/
theorem prime_multiples_avoid (p m n : ℕ) (_hp : Nat.Prime p) (hpm : ¬ p ∣ m) :
    AvoidSum (primeMultiples p n) m := by
  intro hmem
  rw [subsetSums, Finset.mem_filter, Finset.mem_image] at hmem
  obtain ⟨⟨A, hA, hAsum⟩, _⟩ := hmem
  rw [Finset.mem_powerset] at hA
  have hdvd : p ∣ ∑ a ∈ A, a := by
    refine Finset.dvd_sum (fun a ha => ?_)
    have ha' : a ∈ primeMultiples p n := hA ha
    rw [primeMultiples, Finset.mem_filter] at ha'
    exact ha'.2
  rw [hAsum] at hdvd
  exact hpm hdvd

/-! ## Existence: the construction always applies -/

/-- For every `m ≥ 1` there is a prime not dividing `m` (any prime `> m` works). -/
theorem exists_prime_not_dvd (m : ℕ) (hm : 1 ≤ m) : ∃ p, Nat.Prime p ∧ ¬ p ∣ m := by
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (m + 1)
  refine ⟨p, hp, fun hdvd => ?_⟩
  have := Nat.le_of_dvd hm hdvd
  omega

/-- **Existence of an avoiding set.** For every `m ≥ 1` the Erdős–Graham construction yields
    an `m`-avoiding subset of `{1, …, n}` (the multiples of a suitable prime). This is the
    existence statement underlying the lower bound `f(n) ≥ (1/2 + o(1)) · n / log n`. -/
theorem exists_avoiding_multiples (m n : ℕ) (hm : 1 ≤ m) :
    ∃ p, Nat.Prime p ∧ primeMultiples p n ⊆ Icc_n n ∧ AvoidSum (primeMultiples p n) m := by
  obtain ⟨p, hp, hpm⟩ := exists_prime_not_dvd m hm
  exact ⟨p, hp, Finset.filter_subset _ _, prime_multiples_avoid p m n hp hpm⟩

/-! ## Quantitative existence via Bertrand's postulate

The bare existence above uses *some* prime `> m`, which may be far larger than `m`
(so `⌊n/p⌋` could be tiny — for instance the smallest prime not dividing `m = lcm{2,…,t}`
grows with `t`). Bertrand's postulate supplies a prime `p` with `m < p ≤ 2m`, pinning the
size of the construction from below: `⌊n/(2m)⌋ ≤ |S|`. -/

/-- A prime `p` strictly larger than a positive `m` cannot divide `m`
    (otherwise `p ≤ m`). -/
theorem prime_gt_not_dvd {p m : ℕ} (hm : 1 ≤ m) (hmp : m < p) : ¬ p ∣ m := by
  intro hdvd
  have := Nat.le_of_dvd hm hdvd
  omega

/-- **Quantitative Erdős–Graham construction.** For every `m ≥ 1` and `n`, Bertrand's
    postulate yields a prime with `m < p ≤ 2m`; the multiples of `p` in `{1,…,n}` then form an
    `m`-avoiding subset of size `⌊n/p⌋ ≥ ⌊n/(2m)⌋`. This strengthens `exists_avoiding_multiples`
    from bare existence to an explicit lower bound on the avoiding-set size (with the prime
    controlled to within a factor of two of `m`). -/
theorem exists_avoiding_multiples_quantitative (m n : ℕ) (hm : 1 ≤ m) :
    ∃ p, Nat.Prime p ∧ m < p ∧ p ≤ 2 * m ∧
      primeMultiples p n ⊆ Icc_n n ∧
      AvoidSum (primeMultiples p n) m ∧
      n / (2 * m) ≤ (primeMultiples p n).card := by
  obtain ⟨p, hp, hmp, hp2m⟩ := Nat.exists_prime_lt_and_le_two_mul m (by omega)
  refine ⟨p, hp, hmp, hp2m, Finset.filter_subset _ _,
    prime_multiples_avoid p m n hp (prime_gt_not_dvd hm hmp), ?_⟩
  rw [prime_multiples_size]
  exact Nat.div_le_div_left hp2m hp.pos

/-! ## The base case `m = 1`

The Erdős–Graham asymptotics concern general `m`, but the smallest case `m = 1` is exact and
elementary: a set avoids the sum `1` precisely when it does not contain the element `1`. The
only nonempty subset of positive integers that can sum to `1` is the singleton `{1}` itself,
so `1` is a subset sum iff `1 ∈ S`. Consequently the largest `1`-avoiding subset of `{1,…,n}`
is `{2,…,n}`, of size `n − 1`. -/

/-- `1` is a positive subset sum of `S` iff `1 ∈ S`: the only way to add distinct nonnegative
    integers to `1` is to use the element `1` alone (every other element is `0` or `≥ 2`). -/
theorem one_mem_subsetSums_iff (S : Finset ℕ) :
    (1 : ℕ) ∈ subsetSums S ↔ 1 ∈ S := by
  constructor
  · intro h
    rw [subsetSums, Finset.mem_filter, Finset.mem_image] at h
    obtain ⟨⟨A, hA, hAsum⟩, _⟩ := h
    rw [Finset.mem_powerset] at hA
    have h1A : (1 : ℕ) ∈ A := by
      by_contra h1
      have hz : ∀ a ∈ A, a = 0 := by
        intro a ha
        by_contra ha0
        have hane1 : a ≠ 1 := fun he => h1 (he ▸ ha)
        have ha2 : 2 ≤ a := by omega
        have hge : 2 ≤ ∑ x ∈ A, x :=
          le_trans ha2 (Finset.single_le_sum (fun i _ => Nat.zero_le i) ha)
        omega
      have : ∑ a ∈ A, a = 0 := Finset.sum_eq_zero hz
      omega
    exact hA h1A
  · intro h
    rw [subsetSums, Finset.mem_filter, Finset.mem_image]
    refine ⟨⟨{1}, ?_, ?_⟩, by norm_num⟩
    · rw [Finset.mem_powerset]; exact Finset.singleton_subset_iff.mpr h
    · simp

/-- **The base case `m = 1`.** `S` avoids the subset sum `1` iff `1 ∉ S`. Immediate from
    `one_mem_subsetSums_iff` by negation. Hence the largest `1`-avoiding subset of `{1,…,n}`
    is `{2,…,n}` of size `n − 1`, matching the exact value `f(n) = n − 1` at `m = 1`. -/
theorem avoid_one_iff (S : Finset ℕ) : AvoidSum S 1 ↔ 1 ∉ S := by
  unfold AvoidSum
  rw [one_mem_subsetSums_iff]

/-- **Exact `m = 1` realization.** The explicit set `{2, …, n}` witnesses the value
    `f(n) = n − 1` at `m = 1`: it sits inside `{1, …, n}`, avoids the subset sum `1`
    (since `1 ∉ {2,…,n}`, via `avoid_one_iff`), and has cardinality `n − 1`. -/
theorem Icc_two_n_avoid_one (n : ℕ) :
    Finset.Icc 2 n ⊆ Icc_n n ∧
      AvoidSum (Finset.Icc 2 n) 1 ∧
      (Finset.Icc 2 n).card = n - 1 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold Icc_n
    exact Finset.Icc_subset_Icc (by norm_num) le_rfl
  · rw [avoid_one_iff]
    simp only [Finset.mem_Icc]
    omega
  · rw [Nat.card_Icc]
    omega

/-- **Optimality at `m = 1`.** Every `1`-avoiding subset of `{1, …, n}` has size at
    most `n − 1`: avoiding `1` forces `1 ∉ S` (`avoid_one_iff`), so `S ⊆ {2, …, n}`.
    Together with `Icc_two_n_avoid_one` this pins the exact maximum `f(n) = n − 1`
    at `m = 1`. -/
theorem avoid_one_card_le (n : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc_n n)
    (hav : AvoidSum S 1) : S.card ≤ n - 1 := by
  rw [avoid_one_iff] at hav
  have hsub : S ⊆ Finset.Icc 2 n := by
    intro x hx
    have hx1 : x ∈ Icc_n n := hS hx
    unfold Icc_n at hx1
    rw [Finset.mem_Icc] at hx1 ⊢
    have hxne : x ≠ 1 := fun h => hav (h ▸ hx)
    omega
  calc S.card ≤ (Finset.Icc 2 n).card := Finset.card_le_card hsub
    _ = n - 1 := by rw [Nat.card_Icc]; omega

/-! ## The next case `m = 2`

The case `m = 2` is just as exact and elementary as `m = 1`. Among distinct positive integers
the only nonempty subset summing to `2` is the singleton `{2}` (any element `≥ 3` already
overshoots, and the elements `{0, 1}` together sum to only `1`), so `2` is a subset sum iff
`2 ∈ S`. Hence the largest `2`-avoiding subset of `{1,…,n}` (for `n ≥ 2`) is `{1,…,n} ∖ {2}`,
again of size `n − 1`: like `m = 1`, the constraint `m = 2` does not push the value below
`n − 1`. -/

/-- `2` is a positive subset sum of `S` iff `2 ∈ S`: the only nonempty set of distinct
    naturals summing to `2` is `{2}` (an element `≥ 3` overshoots; the remaining candidates
    `{0, 1}` sum to at most `1`). -/
theorem two_mem_subsetSums_iff (S : Finset ℕ) :
    (2 : ℕ) ∈ subsetSums S ↔ 2 ∈ S := by
  constructor
  · intro h
    rw [subsetSums, Finset.mem_filter, Finset.mem_image] at h
    obtain ⟨⟨A, hA, hAsum⟩, _⟩ := h
    rw [Finset.mem_powerset] at hA
    have h2A : (2 : ℕ) ∈ A := by
      by_contra h2
      have hle : ∀ a ∈ A, a ≤ 1 := by
        intro a ha
        by_contra ha1
        have ha2 : a ≠ 2 := fun he => h2 (he ▸ ha)
        have ha3 : 3 ≤ a := by omega
        have hge : 3 ≤ ∑ x ∈ A, x :=
          le_trans ha3 (Finset.single_le_sum (fun i _ => Nat.zero_le i) ha)
        omega
      have hsub : A ⊆ {0, 1} := by
        intro a ha
        have := hle a ha
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      have hbound : ∑ x ∈ A, x ≤ ∑ x ∈ ({0, 1} : Finset ℕ), x :=
        Finset.sum_le_sum_of_subset hsub
      rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)] at hbound
      omega
    exact hA h2A
  · intro h
    rw [subsetSums, Finset.mem_filter, Finset.mem_image]
    refine ⟨⟨{2}, ?_, ?_⟩, by norm_num⟩
    · rw [Finset.mem_powerset]; exact Finset.singleton_subset_iff.mpr h
    · simp

/-- **The case `m = 2`.** `S` avoids the subset sum `2` iff `2 ∉ S`. Immediate from
    `two_mem_subsetSums_iff` by negation. -/
theorem avoid_two_iff (S : Finset ℕ) : AvoidSum S 2 ↔ 2 ∉ S := by
  unfold AvoidSum
  rw [two_mem_subsetSums_iff]

/-- **Exact `m = 2` realization.** For `n ≥ 2` the explicit set `{1,…,n} ∖ {2}` witnesses the
    value `n − 1` at `m = 2`: it sits inside `{1,…,n}`, avoids the subset sum `2` (since
    `2 ∉ {1,…,n} ∖ {2}`, via `avoid_two_iff`), and has cardinality `n − 1`. -/
theorem Icc_erase_two_avoid_two (n : ℕ) (hn : 2 ≤ n) :
    (Icc_n n).erase 2 ⊆ Icc_n n ∧
      AvoidSum ((Icc_n n).erase 2) 2 ∧
      ((Icc_n n).erase 2).card = n - 1 := by
  have hmem : (2 : ℕ) ∈ Icc_n n := by rw [Icc_n, Finset.mem_Icc]; omega
  refine ⟨Finset.erase_subset _ _, ?_, ?_⟩
  · rw [avoid_two_iff]
    exact Finset.notMem_erase 2 _
  · rw [Finset.card_erase_of_mem hmem, Icc_n, Nat.card_Icc]
    omega

/-- **Optimality at `m = 2`.** For `n ≥ 2` every `2`-avoiding subset of `{1,…,n}` has size at
    most `n − 1`: avoiding `2` forces `2 ∉ S` (`avoid_two_iff`), so `S ⊆ {1,…,n} ∖ {2}`.
    Together with `Icc_erase_two_avoid_two` this pins the exact maximum `n − 1` at `m = 2`. -/
theorem avoid_two_card_le (n : ℕ) (hn : 2 ≤ n) (S : Finset ℕ) (hS : S ⊆ Icc_n n)
    (hav : AvoidSum S 2) : S.card ≤ n - 1 := by
  rw [avoid_two_iff] at hav
  have hmem : (2 : ℕ) ∈ Icc_n n := by rw [Icc_n, Finset.mem_Icc]; omega
  have hsub : S ⊆ (Icc_n n).erase 2 := by
    intro x hx
    rw [Finset.mem_erase]
    exact ⟨fun h => hav (h ▸ hx), hS hx⟩
  calc S.card ≤ ((Icc_n n).erase 2).card := Finset.card_le_card hsub
    _ = n - 1 := by rw [Finset.card_erase_of_mem hmem, Icc_n, Nat.card_Icc]; omega

/-! ## The case `m = 3`: the value first drops below `n − 1`

Unlike `m = 1` and `m = 2`, the constraint `m = 3` genuinely lowers the maximum. The number
`3` has **two** representations as a sum of distinct positive integers: `3 = {3}` and
`3 = {1, 2}`. So avoiding the subset sum `3` requires *both* `3 ∉ S` *and* not-both-of
`1, 2 ∈ S` — two independent deletions from `{1,…,n}`. Consequently (for `n ≥ 3`) the largest
`3`-avoiding subset has size `n − 2`, strictly below the `n − 1` of the two previous cases.
This is the first case where the Erdős–Graham value `f`-analogue is pushed down, foreshadowing
the eventual `(1/2 + o(1)) · n / log n` decay. -/

/-- `3` is a positive subset sum of `S` iff `3 ∈ S` **or** both `1 ∈ S` and `2 ∈ S`: the only
    nonempty sets of distinct naturals summing to `3` are `{3}` and `{1, 2}` (any element `≥ 4`
    overshoots, and once `3` is excluded the remaining candidates `{0, 1, 2}` reach `3` only by
    using both `1` and `2`). -/
theorem three_mem_subsetSums_iff (S : Finset ℕ) :
    (3 : ℕ) ∈ subsetSums S ↔ (3 ∈ S ∨ (1 ∈ S ∧ 2 ∈ S)) := by
  constructor
  · intro h
    rw [subsetSums, Finset.mem_filter, Finset.mem_image] at h
    obtain ⟨⟨A, hA, hAsum⟩, _⟩ := h
    rw [Finset.mem_powerset] at hA
    have hle : ∀ a ∈ A, a ≤ 3 := by
      intro a ha
      have hsum := Finset.single_le_sum (f := fun x => x) (fun i _ => Nat.zero_le i) ha
      rw [hAsum] at hsum; exact hsum
    by_cases h3 : (3 : ℕ) ∈ A
    · exact Or.inl (hA h3)
    · refine Or.inr ⟨hA ?_, hA ?_⟩
      · by_contra h1
        have hsub : A ⊆ {0, 2} := by
          intro a ha
          have hle3 := hle a ha
          have ha3 : a ≠ 3 := fun he => h3 (he ▸ ha)
          have ha1 : a ≠ 1 := fun he => h1 (he ▸ ha)
          simp only [Finset.mem_insert, Finset.mem_singleton]; omega
        have hbound : ∑ x ∈ A, x ≤ ∑ x ∈ ({0, 2} : Finset ℕ), x :=
          Finset.sum_le_sum_of_subset hsub
        rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 2)] at hbound
        omega
      · by_contra h2
        have hsub : A ⊆ {0, 1} := by
          intro a ha
          have hle3 := hle a ha
          have ha3 : a ≠ 3 := fun he => h3 (he ▸ ha)
          have ha2 : a ≠ 2 := fun he => h2 (he ▸ ha)
          simp only [Finset.mem_insert, Finset.mem_singleton]; omega
        have hbound : ∑ x ∈ A, x ≤ ∑ x ∈ ({0, 1} : Finset ℕ), x :=
          Finset.sum_le_sum_of_subset hsub
        rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)] at hbound
        omega
  · intro h
    rw [subsetSums, Finset.mem_filter, Finset.mem_image]
    rcases h with h3 | ⟨h1, h2⟩
    · refine ⟨⟨{3}, ?_, ?_⟩, by norm_num⟩
      · rw [Finset.mem_powerset]; exact Finset.singleton_subset_iff.mpr h3
      · simp
    · refine ⟨⟨{1, 2}, ?_, ?_⟩, by norm_num⟩
      · rw [Finset.mem_powerset, Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨h1, h2⟩
      · rw [Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2)]

/-- **The case `m = 3`.** `S` avoids the subset sum `3` iff `3 ∉ S` and not both `1, 2 ∈ S`.
    Immediate from `three_mem_subsetSums_iff` by negation (`not_or`, `not_and`). -/
theorem avoid_three_iff (S : Finset ℕ) :
    AvoidSum S 3 ↔ (3 ∉ S ∧ ¬ (1 ∈ S ∧ 2 ∈ S)) := by
  unfold AvoidSum
  rw [three_mem_subsetSums_iff, not_or]

/-- **Exact `m = 3` realization.** For `n ≥ 3` the explicit set `{1,…,n} ∖ {2, 3}` witnesses
    the value `n − 2` at `m = 3`: it lies inside `{1,…,n}`, avoids the subset sum `3` (since
    `3 ∉ S` and `2 ∉ S`, via `avoid_three_iff`), and has cardinality `n − 2`. -/
theorem Icc_erase_two_three_avoid_three (n : ℕ) (hn : 3 ≤ n) :
    (((Icc_n n).erase 2).erase 3) ⊆ Icc_n n ∧
      AvoidSum (((Icc_n n).erase 2).erase 3) 3 ∧
      (((Icc_n n).erase 2).erase 3).card = n - 2 := by
  have h2 : (2 : ℕ) ∈ Icc_n n := by rw [Icc_n, Finset.mem_Icc]; omega
  have h3 : (3 : ℕ) ∈ (Icc_n n).erase 2 := by
    rw [Finset.mem_erase, Icc_n, Finset.mem_Icc]; omega
  refine ⟨(Finset.erase_subset _ _).trans (Finset.erase_subset _ _), ?_, ?_⟩
  · rw [avoid_three_iff]
    refine ⟨Finset.notMem_erase 3 _, ?_⟩
    rintro ⟨_, hmem2⟩
    have hno2 : (2 : ℕ) ∉ (Icc_n n).erase 2 := Finset.notMem_erase 2 _
    exact hno2 (Finset.mem_of_mem_erase hmem2)
  · rw [Finset.card_erase_of_mem h3, Finset.card_erase_of_mem h2, Icc_n, Nat.card_Icc]
    omega

/-- **Optimality at `m = 3`.** For `n ≥ 3` every `3`-avoiding subset of `{1,…,n}` has size at
    most `n − 2`: avoiding `3` forces `3 ∉ S` and (`1 ∉ S` or `2 ∉ S`), so `S` misses `3` and
    at least one of `1, 2` — two distinct elements of `{1,…,n}`. Together with
    `Icc_erase_two_three_avoid_three` this pins the exact maximum `n − 2` at `m = 3`, strictly
    below the `n − 1` of `m = 1, 2`. -/
theorem avoid_three_card_le (n : ℕ) (hn : 3 ≤ n) (S : Finset ℕ) (hS : S ⊆ Icc_n n)
    (hav : AvoidSum S 3) : S.card ≤ n - 2 := by
  rw [avoid_three_iff] at hav
  obtain ⟨h3, h12⟩ := hav
  have h3mem : (3 : ℕ) ∈ Icc_n n := by rw [Icc_n, Finset.mem_Icc]; omega
  rw [not_and_or] at h12
  rcases h12 with h1 | h2
  · have h1mem : (1 : ℕ) ∈ Icc_n n := by rw [Icc_n, Finset.mem_Icc]; omega
    have hsub : S ⊆ ((Icc_n n).erase 1).erase 3 := by
      intro x hx
      rw [Finset.mem_erase, Finset.mem_erase]
      exact ⟨fun he => h3 (he ▸ hx), fun he => h1 (he ▸ hx), hS hx⟩
    calc S.card ≤ (((Icc_n n).erase 1).erase 3).card := Finset.card_le_card hsub
      _ = n - 2 := by
        have h3e : (3 : ℕ) ∈ (Icc_n n).erase 1 := by
          rw [Finset.mem_erase]; exact ⟨by norm_num, h3mem⟩
        rw [Finset.card_erase_of_mem h3e, Finset.card_erase_of_mem h1mem, Icc_n, Nat.card_Icc]
        omega
  · have h2mem : (2 : ℕ) ∈ Icc_n n := by rw [Icc_n, Finset.mem_Icc]; omega
    have hsub : S ⊆ ((Icc_n n).erase 2).erase 3 := by
      intro x hx
      rw [Finset.mem_erase, Finset.mem_erase]
      exact ⟨fun he => h3 (he ▸ hx), fun he => h2 (he ▸ hx), hS hx⟩
    calc S.card ≤ (((Icc_n n).erase 2).erase 3).card := Finset.card_le_card hsub
      _ = n - 2 := by
        have h3e : (3 : ℕ) ∈ (Icc_n n).erase 2 := by
          rw [Finset.mem_erase]; exact ⟨by norm_num, h3mem⟩
        rw [Finset.card_erase_of_mem h3e, Finset.card_erase_of_mem h2mem, Icc_n, Nat.card_Icc]
        omega

/-! ## The case `m = 4`: the first plateau at `n − 2`

Like `m = 3`, the number `4` has **two** representations as a sum of distinct positive integers:
`4 = {4}` and `4 = {1, 3}`. So avoiding the subset sum `4` again costs *two* deletions from
`{1,…,n}` — remove `4`, and break the pair `{1, 3}` — pinning the maximum at `n − 2` (for
`n ≥ 4`), exactly the `m = 3` value. This is the first time the value **stays put** as `m`
increases: `m = 3, 4` both give `n − 2`, the beginning of the `n − ⌈m/2⌉` staircase (each value
is held for two consecutive `m` before dropping). Unlike `m = 3`, the pair `{1, 3}` is a *gap*
pair rather than the consecutive `{1, 2}`, so the crude "excluded element overshoots" bound no
longer identifies it directly; the characterization is instead decided over the `16` subsets of
`{0, 1, 2, 3}`. -/

/-- `4` is a positive subset sum of `S` iff `4 ∈ S` **or** both `1 ∈ S` and `3 ∈ S`: the only
    nonempty sets of distinct naturals summing to `4` are `{4}` and `{1, 3}` (any element `≥ 5`
    overshoots, so all elements lie in `{0, 1, 2, 3}`, over whose `16` subsets the claim is
    decidable). -/
theorem four_mem_subsetSums_iff (S : Finset ℕ) :
    (4 : ℕ) ∈ subsetSums S ↔ (4 ∈ S ∨ (1 ∈ S ∧ 3 ∈ S)) := by
  constructor
  · intro h
    rw [subsetSums, Finset.mem_filter, Finset.mem_image] at h
    obtain ⟨⟨A, hA, hAsum⟩, _⟩ := h
    rw [Finset.mem_powerset] at hA
    have hle : ∀ a ∈ A, a ≤ 4 := by
      intro a ha
      have hsum := Finset.single_le_sum (f := fun x => x) (fun i _ => Nat.zero_le i) ha
      rw [hAsum] at hsum; exact hsum
    by_cases h4 : (4 : ℕ) ∈ A
    · exact Or.inl (hA h4)
    · refine Or.inr ?_
      have hsub : A ⊆ ({0, 1, 2, 3} : Finset ℕ) := by
        intro a ha
        have hle4 := hle a ha
        have ha4 : a ≠ 4 := fun he => h4 (he ▸ ha)
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      have key : ∀ B ∈ ({0, 1, 2, 3} : Finset ℕ).powerset,
          (∑ x ∈ B, x = 4) → (1 ∈ B ∧ 3 ∈ B) := by decide
      obtain ⟨h1, h3⟩ := key A (Finset.mem_powerset.mpr hsub) hAsum
      exact ⟨hA h1, hA h3⟩
  · intro h
    rw [subsetSums, Finset.mem_filter, Finset.mem_image]
    rcases h with h4 | ⟨h1, h3⟩
    · refine ⟨⟨{4}, ?_, ?_⟩, by norm_num⟩
      · rw [Finset.mem_powerset]; exact Finset.singleton_subset_iff.mpr h4
      · simp
    · refine ⟨⟨{1, 3}, ?_, ?_⟩, by norm_num⟩
      · rw [Finset.mem_powerset, Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨h1, h3⟩
      · rw [Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 3)]

/-- **The case `m = 4`.** `S` avoids the subset sum `4` iff `4 ∉ S` and not both `1, 3 ∈ S`.
    Immediate from `four_mem_subsetSums_iff` by negation (`not_or`). -/
theorem avoid_four_iff (S : Finset ℕ) :
    AvoidSum S 4 ↔ (4 ∉ S ∧ ¬ (1 ∈ S ∧ 3 ∈ S)) := by
  unfold AvoidSum
  rw [four_mem_subsetSums_iff, not_or]

/-- **Exact `m = 4` realization.** For `n ≥ 4` the explicit set `{1,…,n} ∖ {3, 4}` witnesses
    the value `n − 2` at `m = 4`: it lies inside `{1,…,n}`, avoids the subset sum `4` (since
    `4 ∉ S` and `3 ∉ S` breaks the pair `{1, 3}`, via `avoid_four_iff`), and has cardinality
    `n − 2`. -/
theorem Icc_erase_three_four_avoid_four (n : ℕ) (hn : 4 ≤ n) :
    (((Icc_n n).erase 3).erase 4) ⊆ Icc_n n ∧
      AvoidSum (((Icc_n n).erase 3).erase 4) 4 ∧
      (((Icc_n n).erase 3).erase 4).card = n - 2 := by
  have h3 : (3 : ℕ) ∈ Icc_n n := by rw [Icc_n, Finset.mem_Icc]; omega
  have h4 : (4 : ℕ) ∈ (Icc_n n).erase 3 := by
    rw [Finset.mem_erase, Icc_n, Finset.mem_Icc]; omega
  refine ⟨(Finset.erase_subset _ _).trans (Finset.erase_subset _ _), ?_, ?_⟩
  · rw [avoid_four_iff]
    refine ⟨Finset.notMem_erase 4 _, ?_⟩
    rintro ⟨_, hmem3⟩
    have hno3 : (3 : ℕ) ∉ (Icc_n n).erase 3 := Finset.notMem_erase 3 _
    exact hno3 (Finset.mem_of_mem_erase hmem3)
  · rw [Finset.card_erase_of_mem h4, Finset.card_erase_of_mem h3, Icc_n, Nat.card_Icc]
    omega

/-- **Optimality at `m = 4`.** For `n ≥ 4` every `4`-avoiding subset of `{1,…,n}` has size at
    most `n − 2`: avoiding `4` forces `4 ∉ S` and (`1 ∉ S` or `3 ∉ S`), so `S` misses `4` and at
    least one of `1, 3` — two distinct elements of `{1,…,n}`. Together with
    `Icc_erase_three_four_avoid_four` this pins the exact maximum `n − 2` at `m = 4`, equal to
    the `m = 3` value — the first plateau of the `n − ⌈m/2⌉` staircase. -/
theorem avoid_four_card_le (n : ℕ) (hn : 4 ≤ n) (S : Finset ℕ) (hS : S ⊆ Icc_n n)
    (hav : AvoidSum S 4) : S.card ≤ n - 2 := by
  rw [avoid_four_iff] at hav
  obtain ⟨h4, h13⟩ := hav
  have h4mem : (4 : ℕ) ∈ Icc_n n := by rw [Icc_n, Finset.mem_Icc]; omega
  rw [not_and_or] at h13
  rcases h13 with h1 | h3
  · have h1mem : (1 : ℕ) ∈ Icc_n n := by rw [Icc_n, Finset.mem_Icc]; omega
    have hsub : S ⊆ ((Icc_n n).erase 1).erase 4 := by
      intro x hx
      rw [Finset.mem_erase, Finset.mem_erase]
      exact ⟨fun he => h4 (he ▸ hx), fun he => h1 (he ▸ hx), hS hx⟩
    calc S.card ≤ (((Icc_n n).erase 1).erase 4).card := Finset.card_le_card hsub
      _ = n - 2 := by
        have h4e : (4 : ℕ) ∈ (Icc_n n).erase 1 := by
          rw [Finset.mem_erase]; exact ⟨by norm_num, h4mem⟩
        rw [Finset.card_erase_of_mem h4e, Finset.card_erase_of_mem h1mem, Icc_n, Nat.card_Icc]
        omega
  · have h3mem : (3 : ℕ) ∈ Icc_n n := by rw [Icc_n, Finset.mem_Icc]; omega
    have hsub : S ⊆ ((Icc_n n).erase 3).erase 4 := by
      intro x hx
      rw [Finset.mem_erase, Finset.mem_erase]
      exact ⟨fun he => h4 (he ▸ hx), fun he => h3 (he ▸ hx), hS hx⟩
    calc S.card ≤ (((Icc_n n).erase 3).erase 4).card := Finset.card_le_card hsub
      _ = n - 2 := by
        have h4e : (4 : ℕ) ∈ (Icc_n n).erase 3 := by
          rw [Finset.mem_erase]; exact ⟨by norm_num, h4mem⟩
        rw [Finset.card_erase_of_mem h4e, Finset.card_erase_of_mem h3mem, Icc_n, Nat.card_Icc]
        omega

/-! ## Summary

Verified here (0 axioms, 0 sorries): the elementary Erdős–Graham construction behind the
lower bound for `f(n)` — the multiples of a prime `p` in `{1,…,n}` have size `⌊n/p⌋`, avoid
any `m` with `p ∤ m`, and such a prime exists for every `m ≥ 1`; and, via Bertrand's
postulate, an `m`-avoiding subset of size `≥ ⌊n/(2m)⌋` exists for every `m ≥ 1`. The two
smallest cases are pinned exactly: at `m = 1` and (for `n ≥ 2`) at `m = 2` the largest
avoiding subset of `{1,…,n}` has size `n − 1`, realized by `{1,…,n} ∖ {m}`; at `m = 3`
(for `n ≥ 3`) the maximum drops to `n − 2`, realized by `{1,…,n} ∖ {2, 3}` — the first case
where the two representations `3 = {3} = {1,2}` force a second deletion; and at `m = 4`
(for `n ≥ 4`) it **stays** at `n − 2`, realized by `{1,…,n} ∖ {3, 4}` breaking the gap pair
`4 = {4} = {1,3}` — the first plateau of the `n − ⌈m/2⌉` staircase (each value held for two
consecutive `m`). The deep asymptotics (the matching `(1/2 + o(1)) n / log n` lower and upper
bounds) are not addressed here.
-/

end Erdos771Construction
