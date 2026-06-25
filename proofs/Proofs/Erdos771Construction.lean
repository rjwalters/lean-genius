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

/-! ## Summary

Verified here (0 axioms, 0 sorries): the elementary Erdős–Graham construction behind the
lower bound for `f(n)` — the multiples of a prime `p` in `{1,…,n}` have size `⌊n/p⌋`, avoid
any `m` with `p ∤ m`, and such a prime exists for every `m ≥ 1`. The deep asymptotics
(the matching `(1/2 + o(1)) n / log n` lower and upper bounds) are not addressed here.
-/

end Erdos771Construction
