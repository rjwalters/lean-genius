/-
Erdős Problem #1094: Least Prime Factor of Binomial Coefficients

For all n ≥ 2k, the least prime factor of C(n,k) is ≤ max(n/k, k),
with only finitely many exceptions. Strengthens Problem 384.

**Known Results:**
- Erdős observed lpf(C(n,k)) ≤ n/k for n sufficiently large depending on k
- Selfridge conjectured this holds for n ≥ k²-1, except C(62,6)
- 14 known exceptions listed by Erdős-Lacampagne-Selfridge (1988)
- Even stronger: maybe lpf(C(n,k)) ≤ max(n/k, 13) with 12 exceptions

**Status:** OPEN

**References:**
- Erdős, Lacampagne, Selfridge (1988, 1993)
- Guy, Unsolved Problems in Number Theory, B31/B33
- Selfridge (1977)
-/

import Mathlib

namespace Erdos1094

-- ## Part 1: Core Definitions

/-- The least prime factor bound: lpf(C(n,k)) ≤ max(n/k, k). -/
def LPFBound (n k : ℕ) : Prop :=
  (n.choose k).minFac ≤ max (n / k) k

/-- A pair (n, k) is an exception if k > 0, n ≥ 2k, and the bound fails. -/
def IsException (n k : ℕ) : Prop :=
  0 < k ∧ 2 * k ≤ n ∧ ¬LPFBound n k

instance (n k : ℕ) : Decidable (LPFBound n k) := by unfold LPFBound; exact inferInstance
instance (n k : ℕ) : Decidable (IsException n k) := by unfold IsException LPFBound; exact inferInstance

-- ## Part 2: The Main Conjecture

/-- **Erdős Problem #1094**: There are only finitely many exceptions
to the least prime factor bound lpf(C(n,k)) ≤ max(n/k, k). -/
def ErdosProblem1094 : Prop :=
  Set.Finite { p : ℕ × ℕ | IsException p.1 p.2 }

-- ## Part 3: Verified Exceptions

-- C(7,3) = 35, minFac(35) = 5, max(7/3, 3) = max(2, 3) = 3, so 5 > 3: EXCEPTION
theorem exception_7_3 : IsException 7 3 := by unfold IsException LPFBound; native_decide

-- C(13,4) = 715, minFac(715) = 5, max(13/4, 4) = max(3, 4) = 4, so 5 > 4: EXCEPTION
theorem exception_13_4 : IsException 13 4 := by native_decide

-- C(14,4) = 1001, minFac(1001) = 7, max(14/4, 4) = max(3, 4) = 4, so 7 > 4: EXCEPTION
theorem exception_14_4 : IsException 14 4 := by native_decide

-- C(23,5): 23/5 = 4, max(4,5) = 5, lpf > 5: EXCEPTION
theorem exception_23_5 : IsException 23 5 := by native_decide

-- C(44,8) is larger but still computable
theorem exception_44_8 : IsException 44 8 := by native_decide

-- C(46,10), C(47,10), C(47,11) - medium size
theorem exception_46_10 : IsException 46 10 := by native_decide

theorem exception_47_10 : IsException 47 10 := by native_decide

theorem exception_47_11 : IsException 47 11 := by native_decide

-- C(62,6) - Selfridge's famous exception
theorem exception_62_6 : IsException 62 6 := by native_decide

-- C(74,10) - medium
theorem exception_74_10 : IsException 74 10 := by native_decide

-- C(94,10) and C(95,10) - medium
theorem exception_94_10 : IsException 94 10 := by native_decide

theorem exception_95_10 : IsException 95 10 := by native_decide

-- C(241,16) ≈ 1.6 × 10²⁷, C(284,28) ≈ 2.4 × 10³⁸
-- Previously axioms, now proved by native_decide
theorem exception_241_16 : IsException 241 16 := by native_decide
theorem exception_284_28 : IsException 284 28 := by native_decide

-- ## Part 4: Verified Non-Exceptions

-- Many pairs satisfy the bound. Let's verify some.

-- C(4,2) = 6, minFac(6) = 2, max(2,2) = 2: SATISFIES
theorem non_exception_4_2 : LPFBound 4 2 := by native_decide

-- C(6,2) = 15, minFac(15) = 3, max(3,2) = 3: SATISFIES
theorem non_exception_6_2 : LPFBound 6 2 := by native_decide

-- C(6,3) = 20, minFac(20) = 2, max(2,3) = 3: SATISFIES
theorem non_exception_6_3 : LPFBound 6 3 := by native_decide

-- C(10,2) = 45, minFac(45) = 3, max(5,2) = 5: SATISFIES
theorem non_exception_10_2 : LPFBound 10 2 := by native_decide

-- C(10,5) = 252, minFac(252) = 2, max(2,5) = 5: SATISFIES
theorem non_exception_10_5 : LPFBound 10 5 := by native_decide

-- C(12,4) = 495, minFac(495) = 3, max(3,4) = 4: SATISFIES (just barely!)
theorem non_exception_12_4 : LPFBound 12 4 := by native_decide

-- C(20,10) = 184756, minFac = 2, max(2,10) = 10: SATISFIES (even case)
theorem non_exception_20_10 : LPFBound 20 10 := by native_decide

-- C(100,2) = 4950, minFac(4950) = 2, max(50,2) = 50: SATISFIES
theorem non_exception_100_2 : LPFBound 100 2 := by native_decide

-- ## Part 5: Basic Properties

/-- When n/k ≥ k (i.e., n ≥ k²), the bound reduces to lpf(C(n,k)) ≤ n/k. -/
theorem bound_simplifies_large (n k : ℕ) (h : k ≤ n / k) :
    LPFBound n k ↔ (n.choose k).minFac ≤ n / k := by
  unfold LPFBound
  rw [max_eq_left h]

/-- When n/k < k (i.e., n < k²), the bound reduces to lpf(C(n,k)) ≤ k. -/
theorem bound_simplifies_small (n k : ℕ) (h : n / k < k) :
    LPFBound n k ↔ (n.choose k).minFac ≤ k := by
  unfold LPFBound
  rw [max_eq_right (le_of_lt h)]

/-- C(n, 0) = 1, and minFac(1) = 1 ≤ anything, so it's never an exception.
    (Also k > 0 is required for exceptions.) -/
theorem not_exception_k_zero (n : ℕ) : ¬IsException n 0 := by
  intro ⟨hk, _, _⟩; omega

/-- C(n, 1) = n, and minFac(n) ≤ n ≤ n/1 = n when n ≥ 2.
    So k = 1 never gives exceptions. -/
theorem bound_k_one (n : ℕ) (hn : n ≥ 2) : LPFBound n 1 := by
  unfold LPFBound
  simp only [Nat.choose_one_right, Nat.div_one]
  calc n.minFac ≤ n := Nat.minFac_le (by omega : 0 < n)
    _ ≤ max n 1 := le_max_left _ _

theorem not_exception_k_one (n : ℕ) : ¬IsException n 1 := by
  intro ⟨_, h2k, hbound⟩
  exact hbound (bound_k_one n (by omega))

-- Verified small cases of the n=2k bound
theorem bound_4_2 : LPFBound 4 2 := by native_decide
theorem bound_6_3 : LPFBound 6 3 := by native_decide
theorem bound_8_4 : LPFBound 8 4 := by native_decide
theorem bound_10_5 : LPFBound 10 5 := by native_decide
theorem bound_14_7 : LPFBound 14 7 := by native_decide
theorem bound_20_10 : LPFBound 20 10 := by native_decide

-- ## Part 6: Selfridge's Refinement

/-- Selfridge's conjecture: the bound holds for all n ≥ k² - 1,
    with the sole exception of C(62, 6). -/
def SelfridgeConjecture : Prop :=
  ∀ n k : ℕ, 0 < k → n ≥ k ^ 2 - 1 → (n, k) ≠ (62, 6) →
    LPFBound n k

-- ## Part 7: Stronger Bounds

/-- Stronger conjecture: lpf(C(n,k)) ≤ max(n/k, √k)
    with only finitely many exceptions. -/
def StrongerBoundSqrt : Prop :=
  Set.Finite { p : ℕ × ℕ |
    let n := p.1; let k := p.2
    0 < k ∧ 2 * k ≤ n ∧
    (n.choose k).minFac > max (n / k) (Nat.sqrt k) }

/-- Strongest conjecture: lpf(C(n,k)) ≤ max(n/k, 13)
    with at most 12 exceptions. -/
def StrongestBound13 : Prop :=
  ∃ S : Finset (ℕ × ℕ), S.card ≤ 12 ∧
    ∀ n k : ℕ, 0 < k → 2 * k ≤ n → (n, k) ∉ S →
      (n.choose k).minFac ≤ max (n / k) 13

-- ## Part 8: Connection to Problem 384

/-- Naive formulation of Problem 384: "if n ≥ 2k, then C(n,k) has a prime
    factor ≤ n/k." This is FALSE — see `erdos384_naive_false` below. -/
def ErdosProblem384_Naive : Prop :=
  ∀ n k : ℕ, 0 < k → 2 * k ≤ n → ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ p ≤ n / k

/-- The naive formulation of Problem 384 is false: C(7,3) = 35 = 5 × 7
    has prime factors 5 and 7, both exceeding ⌊7/3⌋ = 2. The only prime
    ≤ 2 is 2, and 2 ∤ 35. -/
theorem erdos384_naive_false : ¬ErdosProblem384_Naive := by
  intro h
  obtain ⟨p, hp, hd, hle⟩ := h 7 3 (by omega) (by omega)
  -- The only prime ≤ ⌊7/3⌋ = 2 is p = 2 (since p.Prime → 2 ≤ p)
  have h2le := hp.two_le
  have h7d3 : (7 : ℕ) / 3 = 2 := by native_decide
  rw [h7d3] at hle
  have heq : p = 2 := by omega
  subst heq
  -- But 2 ∤ C(7,3) = 35
  have h35 : Nat.choose 7 3 = 35 := by native_decide
  rw [h35] at hd
  exact absurd hd (by decide)

/-- Corrected Problem 384 (Erdős observation): for each k > 0, there exists
    a threshold N(k) such that for all n ≥ N(k) with n ≥ 2k,
    lpf(C(n,k)) ≤ n/k. This is the actual mathematical statement. -/
def ErdosProblem384 : Prop :=
  ∀ k : ℕ, 0 < k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 2 * k ≤ n →
    (n.choose k).minFac ≤ n / k

-- The relationship: if #1094 holds (finitely many exceptions to the max(n/k,k)
-- bound), then for each fixed k, sufficiently large n satisfies the n/k bound
-- (since max(n/k, k) = n/k when n ≥ k²). This follows from basic set theory
-- but the formal proof requires extracting bounds from finite sets.

-- ## Part 9: Binomial Coefficient Properties

-- Verified: C(n,k) > 1 for small specific cases
theorem choose_gt_one_3_1 : (3 : ℕ).choose 1 > 1 := by native_decide
theorem choose_gt_one_4_2 : (4 : ℕ).choose 2 > 1 := by native_decide
theorem choose_gt_one_5_2 : (5 : ℕ).choose 2 > 1 := by native_decide
theorem choose_gt_one_10_3 : (10 : ℕ).choose 3 > 1 := by native_decide

-- ## Part 10: Summary

/-
**Erdős Problem #1094: OPEN**

**Conjecture:** For n ≥ 2k, lpf(C(n,k)) ≤ max(n/k, k) with finitely many exceptions.

**What we proved:**
- All 14 known exceptions verified computationally (native_decide)
- 8 non-exception cases verified
- k=0 never exception, k=1 never exception (structural proofs)
- Bound simplification for n ≥ k² and n < k²
- C(n,k) > 1 for specific small cases
- The naive formulation of Problem 384 (∀ n ≥ 2k, ∃ prime ≤ n/k dividing C(n,k))
  is FALSE: C(7,3) = 35 has only prime factors 5 and 7, both > ⌊7/3⌋ = 2
- Corrected Problem 384 uses a sufficiency-large-n condition

**What remains open:**
- The finiteness conjecture itself
- Selfridge's conjecture, stronger bounds
- Formal proof that #1094 implies the corrected #384

**Axiom status:** 0 axioms (previously had 1 incorrect axiom asserting #1094 → naive #384)

**References:** ELS88, ELS93, Guy B31/B33
-/

end Erdos1094
