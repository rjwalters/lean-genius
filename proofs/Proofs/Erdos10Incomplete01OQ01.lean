/-
# Erdős Problem #10 — Incomplete 01, Open Question 01
## The exact characterization of the `k = 2` level `mem_two_iff`

Erdős Problem #10 asks whether there is a finite `k` such that every sufficiently large
integer is the sum of a prime and at most `k` powers of `2`.  The parent file
`Erdos10Incomplete01.lean` sets up the family

  `sumPrimeAndTwoPows k = { n | ∃ p (pows : Multiset ℕ),
                                p.Prime ∧ pows.card ≤ k ∧ n = p + (pows.map (2^·)).sum }`,

and pins down the two smallest budgets *exactly*:

* `mem_zero_iff` — `sumPrimeAndTwoPows 0` is exactly the primes;
* `mem_one_iff`  — `n ∈ sumPrimeAndTwoPows 1` iff `n` is prime or `n = p + 2^a`.

This file supplies the **next** exact level, closing the natural gap left open by the parent:

* `mem_two_iff`  — `n ∈ sumPrimeAndTwoPows 2` iff `n` is prime, or `n = p + 2^a`,
  or `n = p + 2^a + 2^b` for a prime `p` and exponents `a, b`.

The characterization is *tight*: the three disjuncts correspond exactly to using `0`, `1`,
or `2` powers of two.  The forward direction splits on `pows.card ∈ {0, 1, 2}` (using
`Multiset.card_eq_zero / _one / _two`); the reverse direction exhibits an explicit multiset of
exponents of the appropriate cardinality.  Everything is elementary and **axiom-free**.

The definition and helper lemmas are restated here so that the file is self-contained and
verifiable against Mathlib alone (it mirrors `Erdos10Incomplete01.lean` verbatim).

## References
- Erdős, P. (1950). "On integers of the form `2^k + p` and some related problems."
  Summa Brasiliensis Mathematicae 2, 113–123.
- Erdős, P.; Graham, R. (1980). *Old and New Problems and Results in Combinatorial Number
  Theory.*
- [erdosproblems.com/10](https://www.erdosproblems.com/10)
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic

namespace Erdos10Incomplete01OQ01

/-- The set of natural numbers expressible as a prime plus **at most `k`** powers of `2`.
The powers-of-two component is recorded as a multiset of exponents of cardinality `≤ k`
(so repeated powers, e.g. `2^3 + 2^3`, are permitted).  This matches the definition in the
parent files `Erdos10Problem.lean` / `Erdos10Incomplete01.lean`. -/
def sumPrimeAndTwoPows (k : ℕ) : Set ℕ :=
  { n | ∃ (p : ℕ) (pows : Multiset ℕ),
      p.Prime ∧ pows.card ≤ k ∧ n = p + (pows.map (2 ^ ·)).sum }

/-! ## Membership basics (restated from the parent) -/

/-- Every prime is a member of `sumPrimeAndTwoPows k` for every `k`: use zero powers of two. -/
theorem prime_mem {p : ℕ} (hp : p.Prime) (k : ℕ) : p ∈ sumPrimeAndTwoPows k :=
  ⟨p, 0, hp, by simp, by simp⟩

/-- A prime plus a single power of two lies in `sumPrimeAndTwoPows 1`. -/
theorem prime_add_pow_mem {p : ℕ} (hp : p.Prime) (a : ℕ) :
    p + 2 ^ a ∈ sumPrimeAndTwoPows 1 :=
  ⟨p, {a}, hp, by simp, by simp⟩

/-- The family `sumPrimeAndTwoPows` is increasing in the budget `k`. -/
theorem mem_mono {k k' : ℕ} (h : k ≤ k') :
    sumPrimeAndTwoPows k ⊆ sumPrimeAndTwoPows k' := by
  rintro n ⟨p, pows, hp, hcard, rfl⟩
  exact ⟨p, pows, hp, hcard.trans h, rfl⟩

/-- A prime plus two powers of two lies in `sumPrimeAndTwoPows 2`. -/
theorem prime_add_two_pows_mem {p : ℕ} (hp : p.Prime) (a b : ℕ) :
    p + 2 ^ a + 2 ^ b ∈ sumPrimeAndTwoPows 2 :=
  ⟨p, a ::ₘ {b}, hp, by simp, by simp [add_assoc]⟩

/-! ## The `k = 2` case, exactly -/

/-- **Exact characterization of the `k = 2` level.**
`n` is a prime plus *at most two* powers of two exactly when one of three things holds:
`n` is prime (zero powers), `n = p + 2^a` (one power), or `n = p + 2^a + 2^b` (two powers),
for a prime `p` and exponents `a, b`.  This is the sharp extension of the parent's
`mem_zero_iff` and `mem_one_iff`. -/
theorem mem_two_iff {n : ℕ} :
    n ∈ sumPrimeAndTwoPows 2 ↔
      n.Prime
      ∨ (∃ p a, p.Prime ∧ n = p + 2 ^ a)
      ∨ (∃ p a b, p.Prime ∧ n = p + 2 ^ a + 2 ^ b) := by
  constructor
  · rintro ⟨p, pows, hp, hcard, rfl⟩
    have hc : pows.card = 0 ∨ pows.card = 1 ∨ pows.card = 2 := by omega
    rcases hc with h0 | h1 | h2
    · -- zero powers: `n` is the prime `p`
      rw [Multiset.card_eq_zero] at h0; subst h0
      left; simpa using hp
    · -- one power: `n = p + 2^a`
      rw [Multiset.card_eq_one] at h1; obtain ⟨a, ha⟩ := h1; subst ha
      right; left; exact ⟨p, a, hp, by simp⟩
    · -- two powers: `n = p + 2^a + 2^b`
      rw [Multiset.card_eq_two] at h2; obtain ⟨a, b, hab⟩ := h2; subst hab
      right; right; exact ⟨p, a, b, hp, by simp [add_assoc]⟩
  · rintro (hp | ⟨p, a, hp, rfl⟩ | ⟨p, a, b, hp, rfl⟩)
    · exact prime_mem hp 2
    · exact mem_mono (by norm_num) (prime_add_pow_mem hp a)
    · exact prime_add_two_pows_mem hp a b

/-- Corollary: any prime plus two (possibly equal) powers of two lands in the `k = 2` level —
the "hardest" of the three disjuncts of `mem_two_iff`, isolated for downstream reuse. -/
theorem two_pows_mem_two {p a b : ℕ} (hp : p.Prime) :
    p + 2 ^ a + 2 ^ b ∈ sumPrimeAndTwoPows 2 :=
  prime_add_two_pows_mem hp a b

#check @mem_two_iff
#check @prime_add_two_pows_mem

end Erdos10Incomplete01OQ01
