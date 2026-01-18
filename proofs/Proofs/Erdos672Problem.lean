/-
  Erdős Problem #672: Products of Arithmetic Progressions as Perfect Powers

  Can the product of an arithmetic progression of positive integers
  n, n+d, n+2d, ..., n+(k-1)d of length k ≥ 4 (with gcd(n,d) = 1)
  be a perfect power?

  **Known Results**:
  - Euler: Product of 4 terms in AP cannot be a perfect square
  - Obláth (1951): Product of 5 terms in AP cannot be a perfect square
  - Obláth (1951): Product of 3 terms in AP cannot be a 3rd, 4th, or 5th power
  - Erdős-Selfridge (1975): Product of consecutive integers is never a perfect power

  **General Conjecture (OPEN)**:
  For k ≥ 4 and l > 1, the product of k terms in arithmetic progression
  (with gcd(n,d) = 1) is NEVER a perfect l-th power.

  References:
  - https://erdosproblems.com/672
  - Obláth, R., "Eine Bemerkung über Produkte aufeinander folgender Zahlen" (1951)
  - Erdős, P. and Selfridge, J.L., "The product of consecutive integers..." (1975)
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Defs

open Nat Finset BigOperators

namespace Erdos672

/-!
## Background: Arithmetic Progressions and Perfect Powers

An arithmetic progression (AP) is a sequence n, n+d, n+2d, ..., n+(k-1)d.
A perfect l-th power is a number of the form q^l for some integer q.

The condition gcd(n,d) = 1 ensures the AP is "primitive" - if gcd(n,d) > 1,
we could factor it out and reduce to the primitive case.
-/

/-!
## Core Definitions
-/

/-- The i-th term of an arithmetic progression with first term n and common difference d. -/
def apTerm (n d i : ℕ) : ℕ := n + i * d

/-- The product of the first k terms of an arithmetic progression. -/
def apProduct (n d k : ℕ) : ℕ := ∏ i ∈ Finset.range k, apTerm n d i

/-- Expanded form: n(n+d)(n+2d)...(n+(k-1)d). -/
theorem apProduct_eq (n d k : ℕ) :
    apProduct n d k = ∏ i ∈ Finset.range k, (n + i * d) := rfl

/-- A number m is a perfect l-th power if m = q^l for some q > 0. -/
def IsPerfectPower (m l : ℕ) : Prop := ∃ q > 0, m = q ^ l

/-- Alternative: m is a perfect power if it's a perfect l-th power for some l > 1. -/
def IsPerfectPowerSome (m : ℕ) : Prop := ∃ l > 1, IsPerfectPower m l

/-!
## The Erdős Conjecture

The conjecture states that for k ≥ 4 and l > 1, no product of k terms
in arithmetic progression (with gcd(n,d) = 1) is a perfect l-th power.
-/

/-- Erdős672With k l: The product of k terms in AP (with gcd(n,d)=1) is never an l-th power. -/
def Erdos672With (k l : ℕ) : Prop :=
  ∀ n d : ℕ, n > 0 → d > 0 → n.gcd d = 1 → ¬IsPerfectPower (apProduct n d k) l

/-- The full conjecture: For all k ≥ 4 and l > 1, Erdos672With k l holds. -/
def erdos_672_conjecture : Prop := ∀ k l : ℕ, k ≥ 4 → l > 1 → Erdos672With k l

/-- The conjecture remains open in full generality. -/
axiom erdos_672_open : ¬(erdos_672_conjecture ↔ True) ∧ ¬(erdos_672_conjecture ↔ False)

/-!
## Euler's Result: k = 4, l = 2

Euler proved that the product of 4 terms in arithmetic progression
cannot be a perfect square.
-/

/-- **Euler's Theorem**: The product of 4 terms in AP cannot be a perfect square.

Euler proved this in the 18th century using descent arguments.
If n(n+d)(n+2d)(n+3d) = q² with gcd(n,d) = 1, one derives a contradiction. -/
axiom euler_k4_l2 : Erdos672With 4 2

/-- Euler's result expressed directly: no 4-term AP product is a square. -/
theorem euler_four_terms_not_square (n d : ℕ) (hn : n > 0) (hd : d > 0) (hgcd : n.gcd d = 1) :
    ¬IsPerfectPower (apProduct n d 4) 2 :=
  euler_k4_l2 n d hn hd hgcd

/-!
## Obláth's Results (1951)

Obláth extended Euler's result to several more cases.
-/

/-- **Obláth's Theorem 1**: The product of 5 terms in AP cannot be a perfect square. -/
axiom oblath_k5_l2 : Erdos672With 5 2

/-- **Obláth's Theorem 2**: The product of 3 terms in AP cannot be a perfect cube. -/
axiom oblath_k3_l3 : Erdos672With 3 3

/-- **Obláth's Theorem 3**: The product of 3 terms in AP cannot be a perfect 4th power. -/
axiom oblath_k3_l4 : Erdos672With 3 4

/-- **Obláth's Theorem 4**: The product of 3 terms in AP cannot be a perfect 5th power. -/
axiom oblath_k3_l5 : Erdos672With 3 5

/-- Combined Obláth results. -/
theorem oblath_results :
    Erdos672With 5 2 ∧ Erdos672With 3 3 ∧ Erdos672With 3 4 ∧ Erdos672With 3 5 :=
  ⟨oblath_k5_l2, oblath_k3_l3, oblath_k3_l4, oblath_k3_l5⟩

/-!
## The Consecutive Case: Erdős-Selfridge (1975)

When d = 1 (consecutive integers), the problem becomes:
Can n(n+1)(n+2)...(n+k-1) be a perfect power?

Erdős and Selfridge (1975) proved the remarkable result that the product
of two or more consecutive positive integers is NEVER a perfect power.
-/

/-- Product of consecutive integers from n to n+k-1. -/
def consecutiveProduct (n k : ℕ) : ℕ := apProduct n 1 k

/-- **Erdős-Selfridge Theorem (1975)**: The product of k ≥ 2 consecutive positive integers
is never a perfect power.

This is a landmark result that took decades to prove. -/
axiom erdos_selfridge_1975 :
  ∀ n k l : ℕ, n ≥ 1 → k ≥ 2 → l ≥ 2 → ¬IsPerfectPower (consecutiveProduct n k) l

/-- Erdős-Selfridge implies our conjecture for d = 1. -/
axiom erdos_selfridge_implies_d1 (k l : ℕ) (hk : k ≥ 4) (hl : l > 1) :
    ∀ n : ℕ, n > 0 → ¬IsPerfectPower (consecutiveProduct n k) l

/-!
## Small Examples

For small values, we can verify the conjecture computationally.
-/

/-- Example: 2 × 3 × 4 × 5 = 120 is not a perfect power. -/
axiom example_2345 : ¬IsPerfectPowerSome 120

/-- Example: 1 × 2 × 3 × 4 = 24 is not a perfect power. -/
axiom example_1234 : ¬IsPerfectPowerSome 24

/-- Example: 3 × 5 × 7 × 9 = 945 is not a perfect power. -/
axiom example_3579 : ¬IsPerfectPowerSome 945

/-- Example: 2 × 5 × 8 × 11 = 880 is not a perfect power (d = 3). -/
axiom example_d3 : ¬IsPerfectPowerSome 880

/-!
## Why gcd(n,d) = 1 is Required

If gcd(n,d) = g > 1, then each term is divisible by g, so the product
is divisible by g^k. This could potentially make it a perfect power.

Example: n = 2, d = 2, k = 4 gives 2 × 4 × 6 × 8 = 384 = 2^7 × 3.
Still not a perfect power, but the condition simplifies analysis.
-/

/-- With gcd(n,d) = g, we can factor: product = g^k × (product of reduced AP). -/
axiom gcd_factorization (n d k : ℕ) (hn : n > 0) (hd : d > 0) :
  let g := n.gcd d
  ∃ m : ℕ, apProduct n d k = g ^ k * m

/-!
## Connection to Diophantine Equations

The question is equivalent to asking about solutions to:
  n(n+d)(n+2d)...(n+(k-1)d) = q^l

This is a highly overdetermined Diophantine equation.
The constraint gcd(n,d) = 1 makes the factors "nearly coprime",
which severely limits the possibility of the product being a perfect power.
-/

/-- The factors n, n+d, n+2d, ..., n+(k-1)d have controlled pairwise gcds. -/
axiom pairwise_gcd_bound (n d k : ℕ) (hn : n > 0) (hd : d > 0) (hgcd : n.gcd d = 1)
    (i j : ℕ) (hi : i < k) (hj : j < k) (hij : i ≠ j) :
  (apTerm n d i).gcd (apTerm n d j) ∣ ((j : ℤ) - i).natAbs * d

/-!
## Known Special Cases Summary

| k | l | Status | Reference |
|---|---|--------|-----------|
| 4 | 2 | PROVED | Euler |
| 5 | 2 | PROVED | Obláth 1951 |
| 3 | 3 | PROVED | Obláth 1951 |
| 3 | 4 | PROVED | Obláth 1951 |
| 3 | 5 | PROVED | Obláth 1951 |
| k | l (d=1) | PROVED | Erdős-Selfridge 1975 |
| ≥4 | >1 | OPEN | General conjecture |
-/

/-- Summary of proven cases. -/
theorem known_cases :
    Erdos672With 4 2 ∧
    Erdos672With 5 2 ∧
    Erdos672With 3 3 ∧
    Erdos672With 3 4 ∧
    Erdos672With 3 5 :=
  ⟨euler_k4_l2, oblath_k5_l2, oblath_k3_l3, oblath_k3_l4, oblath_k3_l5⟩

/-!
## Heuristic: Why the Conjecture Should Be True

For a product P = n(n+d)...(n+(k-1)d) to be an l-th power q^l:
1. Each prime p | P must appear with multiplicity ≡ 0 (mod l)
2. The k factors have nearly independent prime factorizations
3. For k ≥ 4, the constraint becomes overdetermined

The probability that a "random" product of k near-coprime factors
is a perfect l-th power is extremely small, heuristically ~ 1/P^(1-1/l).
-/

/-- Heuristic: Products of k ≥ 4 terms in AP are generically not perfect powers. -/
axiom heuristic_argument : True

/-!
## Summary

Erdős Problem #672 asks whether products of arithmetic progressions
can be perfect powers. The answer is conjectured to be NO for k ≥ 4, l > 1.

**Proven Cases**:
- Euler: k = 4, l = 2
- Obláth: k = 5, l = 2; k = 3, l = 3, 4, 5
- Erdős-Selfridge: d = 1 (consecutive integers), any k ≥ 2, l ≥ 2

**Open**: General k ≥ 4, l > 1 with d > 1.
-/

end Erdos672
