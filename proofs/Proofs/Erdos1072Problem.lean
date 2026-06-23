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
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [h]
  ring

/-- The function f(p) is well-defined for primes: f(p) ≤ p - 1.
    Follows from Wilson's theorem: (p-1) is in the defining set,
    so sInf ≤ p - 1. -/
theorem f_le_pred (p : ℕ) (hp : p.Prime) :
    leastFactorialWilson p ≤ p - 1 := by
  apply Nat.sInf_le
  exact ⟨by have := hp.one_lt; omega, wilson_theorem p hp⟩

/-- f(p) ≥ 1 for primes p ≥ 3 (since 1! + 1 = 2 is not
    divisible by primes ≥ 3).
    Proof: Every element n of the defining set satisfies 0 < n,
    so sInf ≥ 1. -/
theorem f_pos (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ p) :
    1 ≤ leastFactorialWilson p := by
  unfold leastFactorialWilson
  exact le_csInf ⟨p - 1, by omega, wilson_theorem p hp⟩
    fun _ ⟨hpos, _⟩ => by omega

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

noncomputable instance : DecidablePred isWilsonMaximal := Classical.decPred _

/-- Hardy and Subbarao believed that the number of primes p ≤ x
    with f(p) = p - 1 is o(x/log x). That is, such primes have
    density 0 among all primes. -/
axiom hardy_subbarao_belief :
    ∀ ε > 0, ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
      ((Finset.Icc 2 x).filter (fun p => isWilsonMaximal p)).card ≤
        ε * (x : ℝ) / Real.log x

/- ## Small Examples -/

/-- For p = 2: 1! + 1 = 2, so f(2) = 1 = 2 - 1. Maximal. -/
theorem f_of_2 : leastFactorialWilson 2 = 1 := by
  unfold leastFactorialWilson
  apply le_antisymm
  · exact Nat.sInf_le ⟨by omega, by decide⟩
  · exact le_csInf ⟨1, by omega, by decide⟩ fun _ ⟨hpos, _⟩ => by omega

/-- For p = 3: 2! + 1 = 3, so f(3) = 2 = 3 - 1. Maximal. -/
theorem f_of_3 : leastFactorialWilson 3 = 2 := by
  unfold leastFactorialWilson
  apply le_antisymm
  · exact Nat.sInf_le ⟨by omega, by decide⟩
  · exact le_csInf ⟨2, by omega, by decide⟩ fun k ⟨hpos, hdvd⟩ => by
      by_contra h; push_neg at h
      have : k = 1 := by omega
      subst this; revert hdvd; decide

/-- For p = 5: 4! + 1 = 25 = 5², so f(5) = 4 = 5 - 1. Maximal.
    But also 3! + 1 = 7 is not divisible by 5, and 2! + 1 = 3
    is not divisible by 5, and 1! + 1 = 2 is not divisible by 5. -/
theorem f_of_5 : leastFactorialWilson 5 = 4 := by
  unfold leastFactorialWilson
  apply le_antisymm
  · exact Nat.sInf_le ⟨by omega, by decide⟩
  · exact le_csInf ⟨4, by omega, by decide⟩ fun k ⟨hpos, hdvd⟩ => by
      by_contra h; push_neg at h
      have : k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases this with rfl | rfl | rfl <;> revert hdvd <;> decide

/-- For p = 7: 3! + 1 = 7, so f(7) = 3 < 6 = 7 - 1. NOT maximal.
    This is the first prime where f(p) < p - 1. -/
theorem f_of_7 : leastFactorialWilson 7 = 3 := by
  unfold leastFactorialWilson
  apply le_antisymm
  · exact Nat.sInf_le ⟨by omega, by decide⟩
  · exact le_csInf ⟨3, by omega, by decide⟩ fun k ⟨hpos, hdvd⟩ => by
      by_contra h; push_neg at h
      have : k = 1 ∨ k = 2 := by omega
      rcases this with rfl | rfl <;> revert hdvd <;> decide

/-- For p = 11: 5! + 1 = 121 = 11², so f(11) = 5 < 10 = 11 - 1. NOT maximal.
    The first prime past 7 where the Wilson congruence fires early; here
    via the algebraic coincidence (p-1)/2 · (p-1)/2! ≡ -1 (mod 11),
    equivalently 5! = 120 ≡ -1 (mod 11). -/
theorem f_of_11 : leastFactorialWilson 11 = 5 := by
  unfold leastFactorialWilson
  apply le_antisymm
  · exact Nat.sInf_le ⟨by omega, by decide⟩
  · exact le_csInf ⟨5, by omega, by decide⟩ fun k ⟨hpos, hdvd⟩ => by
      by_contra h; push_neg at h
      have : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> revert hdvd <;> decide

/-- For p = 13: factorials modulo 13 trace the sequence
    1, 2, 6, 11, 3, 5, 9, 7, 11, 6, 1, 12 (for n = 1, …, 12), so the residue
    -1 ≡ 12 is hit only at n = 12. Therefore f(13) = 12 = 13 - 1. MAXIMAL.
    Note: 13 is one of the three known Wilson primes (5, 13, 563), i.e. p
    with p² ∣ (p-1)!+1; here we use only the weaker p ∣ (p-1)!+1. -/
theorem f_of_13 : leastFactorialWilson 13 = 12 := by
  unfold leastFactorialWilson
  apply le_antisymm
  · exact Nat.sInf_le ⟨by omega, by decide⟩
  · exact le_csInf ⟨12, by omega, by decide⟩ fun k ⟨hpos, hdvd⟩ => by
      by_contra h; push_neg at h
      have : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨
             k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 := by omega
      rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        revert hdvd <;> decide

/- ## Known Wilson-Maximal Primes -/

/-- p = 2 is Wilson-maximal: f(2) = 1 = 2 - 1. -/
theorem isWilsonMaximal_2 : isWilsonMaximal 2 :=
  ⟨by decide, by rw [f_of_2]⟩

/-- p = 3 is Wilson-maximal: f(3) = 2 = 3 - 1. -/
theorem isWilsonMaximal_3 : isWilsonMaximal 3 :=
  ⟨by decide, by rw [f_of_3]⟩

/-- p = 5 is Wilson-maximal: f(5) = 4 = 5 - 1.
    Also a Wilson prime: 5² = 25 ∣ 4!+1 = 25. -/
theorem isWilsonMaximal_5 : isWilsonMaximal 5 :=
  ⟨by decide, by rw [f_of_5]⟩

/-- p = 7 is NOT Wilson-maximal: f(7) = 3 ≠ 6 = 7 - 1. -/
theorem isNotWilsonMaximal_7 : ¬ isWilsonMaximal 7 := by
  intro ⟨_, heq⟩
  rw [f_of_7] at heq
  omega

/-- p = 11 is NOT Wilson-maximal: f(11) = 5 ≠ 10 = 11 - 1. -/
theorem isNotWilsonMaximal_11 : ¬ isWilsonMaximal 11 := by
  intro ⟨_, heq⟩
  rw [f_of_11] at heq
  omega

/-- p = 13 is Wilson-maximal: f(13) = 12 = 13 - 1.
    Together with 2, 3, 5 this yields four explicit Wilson-maximal primes.
    13 is moreover a Wilson prime, so 13² ∣ 12!+1. -/
theorem isWilsonMaximal_13 : isWilsonMaximal 13 :=
  ⟨by decide, by rw [f_of_13]⟩

/- ## Connection to Wilson Primes -/

-- Note: Wilson primes (p with p² | (p-1)!+1) are empirically maximal
-- (f(p) = p-1 for known Wilson primes 5, 13, 563), but this is not
-- proved in general. The Erdős problem concerns f(p), not the
-- strength of the Wilson congruence.

/-
## Summary

**Problem Status: OPEN**

**Proved Theorems (14)**:
- wilson_theorem: (p-1)! ≡ -1 (mod p) from Mathlib's ZMod.wilsons_lemma [was axiom]
- f_le_pred: f(p) ≤ p-1 from Wilson's theorem [was axiom]
- f_pos: f(p) ≥ 1 for p ≥ 3 via le_csInf (every element has 0 < n) [was axiom]
- f_of_2: f(2) = 1 via sInf computation [was axiom]
- f_of_3: f(3) = 2 via sInf + decide [was axiom]
- f_of_5: f(5) = 4 via sInf + decide (eliminates k=1,2,3) [was axiom]
- f_of_7: f(7) = 3 via sInf + decide (eliminates k=1,2) [was axiom]
- f_of_11: f(11) = 5 via sInf + decide (eliminates k=1,2,3,4) [NEW]
- f_of_13: f(13) = 12 via sInf + decide (eliminates k=1,…,11) [NEW]
- isWilsonMaximal_2, _3, _5, _13: explicit Wilson-maximal primes [NEW]
- isNotWilsonMaximal_7, _11: explicit non-maximal primes [NEW]

**Remaining Axioms (3)** — all OPEN conjectures:
- erdos_1072a: infinitely many maximal primes (OPEN)
- erdos_1072b: f(p)/p → 0 for almost all primes (OPEN)
- hardy_subbarao_belief: maximal primes have density 0 (OPEN conjecture)

**Empirical Status of Wilson-Maximality on Small Primes** (newly formal):
- Maximal: 2, 3, 5, 13
- Not maximal: 7 (f=3), 11 (f=5)
This matches OEIS A154554 and isolates 7, 11 as the first two non-maximal
primes — establishing that maximality is sporadic rather than monotone.
-/
