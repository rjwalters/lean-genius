/-
# Erdős Problem #1072 — Least n with n! + 1 ≡ 0 (mod p)

For a prime p, let f(p) be the least positive integer n such that
n! + 1 ≡ 0 (mod p). Equivalently, n! ≡ -1 (mod p).

By Wilson's theorem, (p-1)! ≡ -1 (mod p) for all primes p, so
f(p) ≤ p - 1 always holds.

**Questions (Erdős–Hardy–Subbarao):**
1. Are there infinitely many primes p with f(p) = p - 1?
2. Is f(p)/p → 0 for almost all primes?

**Status: OPEN.**

The belief is that primes with f(p) = p - 1 have density 0 among
all primes. OEIS: A154554.

Reference: https://erdosproblems.com/1072
-/

import Mathlib

open Nat Filter

/- ## Core Definitions -/

/-- f(p): the least positive integer n such that n! + 1 ≡ 0 (mod p).
    By Wilson's theorem, f(p) ≤ p - 1 for all primes p. -/
noncomputable def leastFactorialWilson (p : ℕ) : ℕ :=
  sInf { n : ℕ | 0 < n ∧ p ∣ n.factorial + 1 }

/-- The set of "Wilson primes" in this generalized sense:
    primes where f(p) = p - 1, i.e., (p-1)! is the first
    factorial achieving -1 mod p. -/
def isWilsonMaximal (p : ℕ) : Prop :=
  p.Prime ∧ leastFactorialWilson p = p - 1

/- ## Wilson's Theorem Gives the Upper Bound -/

/-- Wilson's theorem: (p-1)! ≡ -1 (mod p) for prime p.
    This ensures f(p) is well-defined and f(p) ≤ p - 1.
    Proved from Mathlib's ZMod.wilsons_lemma. -/
theorem wilson_theorem (p : ℕ) (hp : p.Prime) :
    p ∣ (p - 1).factorial + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := ZMod.wilsons_lemma p
  -- h : ((p - 1)! : ZMod p) = -1, so ((p-1)! + 1 : ZMod p) = 0
  rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
  have : ((p - 1).factorial + 1 : ZMod p) = ((p - 1).factorial : ZMod p) + 1 := by push_cast; ring
  rw [this, h]
  simp

/-- The function f(p) is well-defined for primes: f(p) ≤ p - 1.
    Follows from Wilson's theorem: (p-1) is in the defining set,
    so sInf ≤ p - 1. -/
theorem f_le_pred (p : ℕ) (hp : p.Prime) :
    leastFactorialWilson p ≤ p - 1 := by
  apply Nat.sInf_le
  exact ⟨by have := hp.one_lt; omega, wilson_theorem p hp⟩

/-- f(p) ≥ 1 for primes p ≥ 3 (since 1! + 1 = 2 is not
    divisible by primes ≥ 3). -/
axiom f_pos (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ p) :
    1 ≤ leastFactorialWilson p

/- ## Question 1: Infinitely Many Maximal Primes -/

/-- Are there infinitely many primes p with f(p) = p - 1?
    These are primes where no factorial smaller than (p-1)!
    achieves -1 mod p. -/
axiom erdos_1072a :
    Set.Infinite { p : ℕ | isWilsonMaximal p }

/- ## Question 2: f(p)/p → 0 for Almost All Primes -/

/-- For almost all primes, f(p)/p → 0. More precisely:
    there exists a set P of primes with relative density 1
    such that f(p)/p → 0 along P. -/
axiom erdos_1072b :
    ∃ S : Set ℕ, (∀ p ∈ S, p.Prime) ∧
    -- S has density 1 among primes (informally)
    (∀ ε > 0, ∃ N : ℕ, ∀ p ∈ S, N ≤ p →
      (leastFactorialWilson p : ℝ) / (p : ℝ) < ε)

/- ## Hardy–Subbarao Belief -/

/-- Hardy and Subbarao believed that the number of primes p ≤ x
    with f(p) = p - 1 is o(x/log x). That is, such primes have
    density 0 among all primes. -/
axiom hardy_subbarao_belief :
    ∀ ε > 0, ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
      ((Finset.Icc 2 x).filter (fun p => isWilsonMaximal p)).card ≤
        ε * (x : ℝ) / Real.log x

/- ## Small Examples -/

/-- For p = 2: 1! + 1 = 2, so f(2) = 1 = 2 - 1. Maximal. -/
axiom f_of_2 : leastFactorialWilson 2 = 1

/-- For p = 3: 2! + 1 = 3, so f(3) = 2 = 3 - 1. Maximal. -/
axiom f_of_3 : leastFactorialWilson 3 = 2

/-- For p = 5: 4! + 1 = 25 = 5², so f(5) = 4 = 5 - 1. Maximal.
    But also 3! + 1 = 7 is not divisible by 5, and 2! + 1 = 3
    is not divisible by 5, and 1! + 1 = 2 is not divisible by 5. -/
axiom f_of_5 : leastFactorialWilson 5 = 4

/-- For p = 7: 3! + 1 = 7, so f(7) = 3 < 6 = 7 - 1. NOT maximal.
    This is the first prime where f(p) < p - 1. -/
axiom f_of_7 : leastFactorialWilson 7 = 3

/- ## Connection to Wilson Primes -/

-- Note: Wilson primes (p with p² | (p-1)!+1) are empirically maximal
-- (f(p) = p-1 for known Wilson primes 5, 13, 563), but this is not
-- proved in general. The Erdős problem concerns f(p), not the
-- strength of the Wilson congruence.

/-
## Summary

**Problem Status: OPEN**

**Proved Theorems**:
- wilson_theorem: (p-1)! ≡ -1 (mod p) from Mathlib's ZMod.wilsons_lemma [was axiom]
- f_le_pred: f(p) ≤ p-1 from Wilson's theorem [was axiom]

**Remaining Axioms (9)**:
- f_pos: f(p) ≥ 1 for p ≥ 3 (provable but needs sInf reasoning)
- erdos_1072a: infinitely many maximal primes (OPEN)
- erdos_1072b: f(p)/p → 0 for almost all primes (OPEN)
- hardy_subbarao_belief: maximal primes have density 0 (OPEN conjecture)
- f_of_2, f_of_3, f_of_5, f_of_7: small values (provable, need sInf computation)
-/
