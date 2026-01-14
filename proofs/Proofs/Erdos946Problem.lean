import Mathlib

/-!
# Erdős Problem 946: Equal Divisor Counts at Consecutive Integers

## What This Proves
We formalize Erdős Problem 946, which asks: are there infinitely many n such
that τ(n) = τ(n+1), where τ is the divisor counting function?

The answer is **yes**: Heath-Brown proved this in 1984, building on earlier
work by Spiro who showed τ(n) = τ(n+5040) infinitely often.

## The Problem
The **divisor function** τ(n) counts the number of positive divisors of n.
For example: τ(1) = 1, τ(2) = 2, τ(6) = 4, τ(12) = 6.

The question asks: do consecutive integers ever have the same number of
divisors? And if so, does this happen infinitely often?

Examples:
- τ(2) = τ(3) = 2 (both are prime)
- τ(14) = τ(15) = 4 (14 = 2×7, 15 = 3×5)

## Historical Context
This problem was posed by Erdős and Mirsky in 1952. The breakthrough came
through Spiro (1981) and Heath-Brown (1984). Bounds on the counting function
were improved by Hildebrand (1987) and Erdős-Pomerance-Sárközy (1987).

## Approach
- **Foundation:** We use Mathlib's divisor counting
- **Axiom Required:** The infinitude result requires analytic number theory
- **Bounds:** We state the known upper and lower bounds as axioms

## Status
- [x] Problem statement formalized
- [x] Main theorem stated
- [x] Uses axioms for analytic results
- [ ] Full constructive proof

## References
- Heath-Brown, D. R., "The divisor function at consecutive integers" (1984)
- Hildebrand, A., Pacific J. Math. (1987)
- https://erdosproblems.com/946
-/

namespace Erdos946

open Nat Filter

/-! ## Definitions -/

/-- The divisor counting function τ(n) = number of divisors of n.
    We use Mathlib's `Nat.divisors` and count its cardinality. -/
def tau (n : ℕ) : ℕ := (Nat.divisors n).card

/-- The set of n where τ(n) = τ(n+1) -/
def consecutiveEqualDivisors : Set ℕ := {n : ℕ | tau n = tau (n + 1)}

/-! ## Concrete Examples -/

/-- τ(1) = 1 (only divisor is 1) -/
example : tau 1 = 1 := by native_decide

/-- τ(2) = 2 (divisors: 1, 2) -/
example : tau 2 = 2 := by native_decide

/-- τ(3) = 2 (divisors: 1, 3) -/
example : tau 3 = 2 := by native_decide

/-- τ(4) = 3 (divisors: 1, 2, 4) -/
example : tau 4 = 3 := by native_decide

/-- τ(6) = 4 (divisors: 1, 2, 3, 6) -/
example : tau 6 = 4 := by native_decide

/-- τ(12) = 6 (divisors: 1, 2, 3, 4, 6, 12) -/
example : tau 12 = 6 := by native_decide

/-- Example: τ(2) = τ(3) = 2 (both are prime) -/
example : tau 2 = tau 3 := by native_decide

/-- Example: τ(14) = τ(15) = 4 -/
example : tau 14 = tau 15 := by native_decide

/-- Example: τ(21) = τ(22) = 4 -/
example : tau 21 = tau 22 := by native_decide

/-! ## Main Theorems -/

/-- **Axiom (Heath-Brown 1984):**
    There are infinitely many n such that τ(n) = τ(n+1).

    Heath-Brown improved Spiro's method to prove this fundamental result. -/
axiom heathBrown_infinitely_many : consecutiveEqualDivisors.Infinite

/-- **Erdős Problem 946** (Solved)

    Are there infinitely many n such that τ(n) = τ(n+1)?

    Yes, proved by Heath-Brown (1984). -/
theorem erdos_946 : consecutiveEqualDivisors.Infinite :=
  heathBrown_infinitely_many

/-! ## Variants -/

/-- **Axiom (Spiro 1981):**
    There are infinitely many n such that τ(n) = τ(n + 5040).

    This was the first breakthrough, using properties of highly composite numbers.
    5040 = 7! has many divisors. -/
axiom spiro_5040 : {n : ℕ | tau n = tau (n + 5040)}.Infinite

/-! ## Notes on Bounds

The counting function N(x) = |{n ≤ x : τ(n) = τ(n+1)}| satisfies:

**Lower bounds:**
- Heath-Brown (1984): N(x) ≥ x / (log x)^7
- Hildebrand (1987): N(x) ≥ x / (log log x)^3

**Upper bound:**
- Erdős-Pomerance-Sárközy (1987): N(x) ≤ x / √(log log x)

The true asymptotic is believed to be c · x / √(log log x) for some c > 0.
Tao and Teräväinen (2025) established this for almost all x. -/

end Erdos946
