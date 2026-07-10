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

/-! ## Summary

Verified here (0 axioms, 0 sorries): the elementary Erdős–Graham construction behind the
lower bound for `f(n)` — the multiples of a prime `p` in `{1,…,n}` have size `⌊n/p⌋`, avoid
any `m` with `p ∤ m`, and such a prime exists for every `m ≥ 1`; and, via Bertrand's
postulate, an `m`-avoiding subset of size `≥ ⌊n/(2m)⌋` exists for every `m ≥ 1`. The two
smallest cases are pinned exactly: at `m = 1` and (for `n ≥ 2`) at `m = 2` the largest
avoiding subset of `{1,…,n}` has size `n − 1`, realized by `{1,…,n} ∖ {m}`. The deep
asymptotics (the matching `(1/2 + o(1)) n / log n` lower and upper bounds) are not addressed
here.
-/

end Erdos771Construction
