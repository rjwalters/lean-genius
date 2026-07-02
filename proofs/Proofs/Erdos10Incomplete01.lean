/-
# Erdős Problem #10 — Incomplete 01
## Foundations for the representation set `prime + at most k powers of 2`

Erdős Problem #10 asks whether there is a finite `k` such that every sufficiently large
integer is the sum of a prime and at most `k` powers of `2`.  Erdős and Graham conjectured
the answer is *no*.  The parent file `Erdos10Problem.lean` introduces the central object

  `sumPrimeAndTwoPows k = { n | ∃ p (pows : Multiset ℕ),
                                p.Prime ∧ pows.card ≤ k ∧ n = p + (pows.map (2^·)).sum }`,

the set of integers representable as a prime plus **at most `k`** powers of `2` (the powers'
exponents are recorded as a multiset, so repeats such as `2^3 + 2^3` are allowed), but proves
nothing about it.  This file supplies the elementary order- and membership-structure of that
family, entirely **without axioms or sorries**:

* `prime_mem`      — every prime lies in `sumPrimeAndTwoPows k` (take zero powers);
* `mem_zero_iff`   — `sumPrimeAndTwoPows 0` is *exactly* the primes;
* `mem_one_iff`    — `n` uses at most one power of two iff `n` is prime or `n = p + 2^a`;
* `prime_add_pow_mem`, `add_pow_mem` — how to build members by adjoining a power of `2`;
* `mem_mono`, `subset_succ` — the family is increasing in `k`;
* `infinite`       — each `sumPrimeAndTwoPows k` is infinite;
* `eventuallyRepresentable` and `mem_iUnion_iff` — the union over all `k`, in whose terms
  the Erdős–Graham conjecture (`erdosGraham`) is stated.

These lemmas make the base definition usable and pin down the two smallest cases exactly;
the genuinely open content (no finite `k` works) is packaged as `erdosGraham`, left as a
`Prop`, not asserted.  The sharper *obstruction* results — e.g. the covering-congruence
argument forcing the prime to be small when `k = 1` — live in the sibling file
`Erdos10OQ01Incomplete01.lean`.

## References
- Erdős, P. (1950). "On integers of the form `2^k + p` and some related problems."
  Summa Brasiliensis Mathematicae 2, 113–123.
- Erdős, P.; Graham, R. (1980). *Old and New Problems and Results in Combinatorial Number
  Theory.*  (The conjecture that no finite `k` suffices.)
- [erdosproblems.com/10](https://www.erdosproblems.com/10)
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic

namespace Erdos10Incomplete01

/-- The set of natural numbers expressible as a prime plus **at most `k`** powers of `2`.
The powers-of-two component is recorded as a multiset of exponents of cardinality `≤ k`
(so repeated powers, e.g. `2^3 + 2^3`, are permitted).  This matches the definition in the
parent file `Erdos10Problem.lean`. -/
def sumPrimeAndTwoPows (k : ℕ) : Set ℕ :=
  { n | ∃ (p : ℕ) (pows : Multiset ℕ),
      p.Prime ∧ pows.card ≤ k ∧ n = p + (pows.map (2 ^ ·)).sum }

/-! ## Membership basics -/

/-- Every prime is a member of `sumPrimeAndTwoPows k` for every `k`: use zero powers of two. -/
theorem prime_mem {p : ℕ} (hp : p.Prime) (k : ℕ) : p ∈ sumPrimeAndTwoPows k :=
  ⟨p, 0, hp, by simp, by simp⟩

/-- Adjoining a fresh power `2^a` to a member of `sumPrimeAndTwoPows k` yields a member of
`sumPrimeAndTwoPows (k+1)`. -/
theorem add_pow_mem {n k : ℕ} (hn : n ∈ sumPrimeAndTwoPows k) (a : ℕ) :
    n + 2 ^ a ∈ sumPrimeAndTwoPows (k + 1) := by
  obtain ⟨p, pows, hp, hcard, rfl⟩ := hn
  refine ⟨p, a ::ₘ pows, hp, ?_, ?_⟩
  · rw [Multiset.card_cons]; omega
  · simp only [Multiset.map_cons, Multiset.sum_cons]; ring

/-- A prime plus a single power of two lies in `sumPrimeAndTwoPows 1`. -/
theorem prime_add_pow_mem {p : ℕ} (hp : p.Prime) (a : ℕ) :
    p + 2 ^ a ∈ sumPrimeAndTwoPows 1 :=
  ⟨p, {a}, hp, by simp, by simp⟩

/-! ## The two smallest cases, exactly -/

/-- `sumPrimeAndTwoPows 0` is precisely the set of primes: with `≤ 0` powers of two the
multiset of exponents is empty, so `n` must equal its prime part. -/
theorem mem_zero_iff {n : ℕ} : n ∈ sumPrimeAndTwoPows 0 ↔ n.Prime := by
  constructor
  · rintro ⟨p, pows, hp, hcard, rfl⟩
    rw [Nat.le_zero, Multiset.card_eq_zero] at hcard
    subst hcard
    simpa using hp
  · intro hp; exact prime_mem hp 0

/-- `n` uses at most one power of two exactly when `n` is prime (zero powers) or `n = p + 2^a`
for a prime `p` and exponent `a` (one power). -/
theorem mem_one_iff {n : ℕ} :
    n ∈ sumPrimeAndTwoPows 1 ↔ n.Prime ∨ ∃ p a, p.Prime ∧ n = p + 2 ^ a := by
  constructor
  · rintro ⟨p, pows, hp, hcard, rfl⟩
    have hc : pows.card = 0 ∨ pows.card = 1 := by omega
    rcases hc with h0 | h1
    · rw [Multiset.card_eq_zero] at h0; subst h0
      left; simpa using hp
    · rw [Multiset.card_eq_one] at h1; obtain ⟨a, ha⟩ := h1; subst ha
      right; exact ⟨p, a, hp, by simp⟩
  · rintro (hp | ⟨p, a, hp, rfl⟩)
    · exact prime_mem hp 1
    · exact prime_add_pow_mem hp a

/-! ## Monotonicity in `k` -/

/-- The family `sumPrimeAndTwoPows` is increasing in the budget `k`: allowing more powers of
two can only enlarge the representable set. -/
theorem mem_mono {k k' : ℕ} (h : k ≤ k') :
    sumPrimeAndTwoPows k ⊆ sumPrimeAndTwoPows k' := by
  rintro n ⟨p, pows, hp, hcard, rfl⟩
  exact ⟨p, pows, hp, hcard.trans h, rfl⟩

/-- Consecutive inclusion, the special case of `mem_mono`. -/
theorem subset_succ (k : ℕ) : sumPrimeAndTwoPows k ⊆ sumPrimeAndTwoPows (k + 1) :=
  mem_mono (Nat.le_succ k)

/-! ## Infinitude -/

/-- Every `sumPrimeAndTwoPows k` is infinite: it already contains all (infinitely many)
primes. -/
theorem infinite (k : ℕ) : (sumPrimeAndTwoPows k).Infinite := by
  have hsub : {p : ℕ | p.Prime} ⊆ sumPrimeAndTwoPows k := fun p hp => prime_mem hp k
  exact Nat.infinite_setOf_prime.mono hsub

/-! ## The union over all budgets, and the conjecture -/

/-- The integers representable as a prime plus finitely many powers of two, for *some* finite
budget `k`. -/
def eventuallyRepresentable : Set ℕ := ⋃ k, sumPrimeAndTwoPows k

/-- Membership in the union unfolds to "some finite `k` works". -/
theorem mem_iUnion_iff {n : ℕ} :
    n ∈ eventuallyRepresentable ↔ ∃ k, n ∈ sumPrimeAndTwoPows k := by
  simp [eventuallyRepresentable]

/-- Each level embeds into the union. -/
theorem subset_eventuallyRepresentable (k : ℕ) :
    sumPrimeAndTwoPows k ⊆ eventuallyRepresentable :=
  Set.subset_iUnion _ k

/-- **Erdős–Graham conjecture (open), stated in terms of the base definition.**
No finite `k` makes every integer `> 1` a prime plus at most `k` powers of two: for each `k`
there is an integer `n > 1` outside `sumPrimeAndTwoPows k`.  This is *not* proved here (it is
open); it is recorded as a proposition so downstream files can refer to it. -/
def erdosGraham : Prop :=
  ∀ k : ℕ, ∃ n : ℕ, 1 < n ∧ n ∉ sumPrimeAndTwoPows k

#check @prime_mem
#check @mem_zero_iff
#check @mem_one_iff
#check @infinite

end Erdos10Incomplete01
