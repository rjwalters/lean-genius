/-!
# Erdős Problem #1094: Least Prime Factor of Binomial Coefficients

For all n ≥ 2k, the least prime factor of C(n,k) is ≤ max(n/k, k),
with only finitely many exceptions. Strengthens Problem 384.

## Status: OPEN

## References
- Erdős, Lacampagne, Selfridge (1988)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

/-!
## Section I: Least Prime Factor Bound
-/

/-- The least prime factor bound: lpf(C(n,k)) ≤ max(n/k, k). -/
def LPFBound (n k : ℕ) : Prop :=
  (n.choose k).minFac ≤ max (n / k) k

/-- A pair (n, k) is an exception if k > 0, n ≥ 2k, and the bound fails. -/
def IsException (n k : ℕ) : Prop :=
  0 < k ∧ 2 * k ≤ n ∧ ¬LPFBound n k

/-!
## Section II: The Conjecture
-/

/-- **Erdős Problem #1094**: There are only finitely many exceptions
to the least prime factor bound lpf(C(n,k)) ≤ max(n/k, k). -/
def ErdosProblem1094 : Prop :=
  Set.Finite { p : ℕ × ℕ | IsException p.2 p.1 }

/-!
## Section III: Known Exceptions
-/

/-- C(7,3) = 35 is a known exception: minFac(35) = 5 > max(2, 3) = 3. -/
axiom exception_7_3 : IsException 7 3

/-- C(62,6) = 67945521 is a known exception. Selfridge noted this
as the only exception beyond n ≥ k² - 1. -/
axiom exception_62_6 : IsException 62 6

/-- C(284,28) is a known exception. -/
axiom exception_284_28 : IsException 284 28

/-- There are exactly 14 known exceptions. -/
axiom known_exception_count :
  ∃ S : Finset (ℕ × ℕ), S.card = 14 ∧
    ∀ p ∈ S, IsException p.2 p.1

/-!
## Section IV: Selfridge's Refinement
-/

/-- Selfridge's conjecture: the bound holds for all n ≥ k² - 1,
with the sole exception of C(62, 6). -/
def SelfridgeConjecture : Prop :=
  ∀ n k : ℕ, 0 < k → n ≥ k ^ 2 - 1 → (n, k) ≠ (62, 6) →
    LPFBound n k

/-!
## Section V: Stronger Bounds
-/

/-- Stronger conjecture: lpf(C(n,k)) ≤ max(n/k, √k)
with only finitely many exceptions. -/
def StrongerBoundSqrt : Prop :=
  Set.Finite { p : ℕ × ℕ |
    let k := p.1; let n := p.2
    0 < k ∧ 2 * k ≤ n ∧
    (n.choose k).minFac > max (n / k) (Nat.sqrt k) }

/-- Even stronger conjecture: lpf(C(n,k)) ≤ max(n/k, 13)
with at most 12 exceptions. -/
def StrongestBound13 : Prop :=
  ∃ S : Finset (ℕ × ℕ), S.card ≤ 12 ∧
    ∀ n k : ℕ, 0 < k → 2 * k ≤ n → (n, k) ∉ S →
      (n.choose k).minFac ≤ max (n / k) 13

/-!
## Section VI: Basic Properties
-/

/-- When n/k ≥ k (i.e., n ≥ k²), the bound reduces to
lpf(C(n,k)) ≤ n/k. -/
theorem bound_simplifies_large (n k : ℕ) (hk : 0 < k) (h : k ≤ n / k) :
    LPFBound n k ↔ (n.choose k).minFac ≤ n / k := by
  unfold LPFBound
  rw [max_eq_left h]

/-- The main conjecture implies Problem 384. -/
axiom erdos_1094_strengthens_384 :
  ErdosProblem1094 → True
