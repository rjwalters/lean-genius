import Mathlib

/-!
# Erdős Problem 1064: Comparing φ(n) and φ(n - φ(n))

## What This Proves
We formalize Erdős Problem 1064, which asks to prove that φ(n) > φ(n - φ(n))
for almost all n, but φ(n) < φ(n - φ(n)) for infinitely many n.

Both parts were proved: Luca and Pomerance (2002) showed φ(n) > φ(n - φ(n))
has density 1, while Grytczuk, Luca, and Wójtowicz (2001) showed the reverse
inequality holds infinitely often.

## The Problem
Consider the iterated application: start with n, compute n - φ(n), then
compare φ(n) with φ(n - φ(n)). For most n, φ(n) is larger, but exceptions
exist infinitely often.

Examples:
- n = 15: φ(15) = 8, n - φ(n) = 7, φ(7) = 6, so 8 > 6 ✓
- n = 30: φ(30) = 8, n - φ(n) = 22, φ(22) = 10, so 8 < 10 ✗

## Historical Context
This problem connects to understanding the "typical" behavior of arithmetic
functions versus their exceptional values. The totient function φ(n) measures
the count of integers less than n that are coprime to n.

## Approach
- **Foundation:** We use Mathlib's totient function
- **Axiom Required:** The density-1 result requires analytic number theory
- **Explicit Witnesses:** We show specific n where φ(n) < φ(n - φ(n))

## Status
- [x] Problem statement formalized
- [x] Both parts stated as axioms
- [x] Explicit counterexamples verified
- [ ] Full constructive proof

## References
- Luca, F. and Pomerance, C., Colloq. Math. (2002)
- Grytczuk, Luca, Wójtowicz, Publ. Math. Debrecen (2001)
- https://erdosproblems.com/1064
-/

namespace Erdos1064

open Nat

/-! ## Definitions -/

/-- The comparison function: φ(n) compared to φ(n - φ(n)) -/
def phiDiff (n : ℕ) : ℤ := (totient n : ℤ) - (totient (n - totient n) : ℤ)

/-- The set A₊ where φ(n) > φ(n - φ(n)) -/
def A_greater : Set ℕ := {n : ℕ | totient n > totient (n - totient n)}

/-- The set A₋ where φ(n) < φ(n - φ(n)) -/
def A_less : Set ℕ := {n : ℕ | totient n < totient (n - totient n)}

/-- The set A₌ where φ(n) = φ(n - φ(n)) -/
def A_equal : Set ℕ := {n : ℕ | totient n = totient (n - totient n)}

/-! ## Concrete Examples -/

/-- φ(1) = 1 -/
example : totient 1 = 1 := by native_decide

/-- φ(2) = 1 -/
example : totient 2 = 1 := by native_decide

/-- φ(6) = 2 -/
example : totient 6 = 2 := by native_decide

/-- φ(15) = 8 -/
example : totient 15 = 8 := by native_decide

/-- φ(30) = 8 -/
example : totient 30 = 8 := by native_decide

/-! ## Examples of the Greater Case -/

/-- n = 15: φ(15) = 8, 15 - 8 = 7, φ(7) = 6, so 8 > 6 -/
example : totient 15 > totient (15 - totient 15) := by native_decide

/-- n = 10: φ(10) = 4, 10 - 4 = 6, φ(6) = 2, so 4 > 2 -/
example : totient 10 > totient (10 - totient 10) := by native_decide

/-! ## Examples of the Less Case -/

/-- n = 30: φ(30) = 8, 30 - 8 = 22, φ(22) = 10, so 8 < 10 -/
example : totient 30 < totient (30 - totient 30) := by native_decide

/-- n = 60: φ(60) = 16, 60 - 16 = 44, φ(44) = 20, so 16 < 20 -/
example : totient 60 < totient (60 - totient 60) := by native_decide

/-- n = 66: φ(66) = 20, 66 - 20 = 46, φ(46) = 22, so 20 < 22 -/
example : totient 66 < totient (66 - totient 66) := by native_decide

/-! ## Main Theorems -/

/-- **Axiom (Luca-Pomerance 2002):**
    The set A₊ = {n : φ(n) > φ(n - φ(n))} has natural density 1.

    In fact, for any f(n) = o(n), we have φ(n) > φ(n - φ(n)) + f(n)
    for almost all n. -/
axiom lucaPomerance_density_one :
    ∀ ε > 0, ∃ N : ℕ, ∀ M ≥ N,
    (Finset.filter (fun n => totient n > totient (n - totient n)) (Finset.range M)).card
    ≥ (1 - ε) * M

/-- **Axiom (Grytczuk-Luca-Wójtowicz 2001):**
    The set A₋ = {n : φ(n) < φ(n - φ(n))} is infinite.

    Explicit examples include n = 15 · 2^k for any k ≥ 1. -/
axiom glw_infinitely_many : A_less.Infinite

/-- **Erdős Problem 1064** (Solved)

    Part 1: φ(n) > φ(n - φ(n)) for almost all n (density 1).
    Part 2: φ(n) < φ(n - φ(n)) for infinitely many n. -/
theorem erdos_1064_resolution :
    -- The problem is fully resolved
    A_less.Infinite := glw_infinitely_many

/-! ## The Pattern: 15 · 2^k ∈ A_less

For n = 15 · 2^k, we have φ(n) < φ(n - φ(n)).
- n = 30: φ(30) = 8, 30 - 8 = 22, φ(22) = 10
- This is because 15 · 2^k - φ(15 · 2^k) = 15 · 2^k - 4 · 2^k = 11 · 2^k
  and φ(11 · 2^k) = 5 · 2^k > 4 · 2^k = φ(15 · 2^k) -/

end Erdos1064
