/-
  Erdős Problem #242: The Erdős-Straus Conjecture

  Source: https://erdosproblems.com/242
  Status: OPEN (verified computationally for n < 10^17, no proof)

  Question:
  For every n > 2, do there exist distinct positive integers x < y < z such that
    4/n = 1/x + 1/y + 1/z ?

  This is the famous Erdős-Straus conjecture, first posed in 1948.

  Known Results:
  - Verified computationally for all n up to 10^17 (various authors)
  - Proved for almost all n in the sense of density
  - Specific constructions exist for various residue classes
  - The conjecture REMAINS OPEN in full generality

  The existence of 4 unit fractions (instead of 3) follows trivially from
  the greedy algorithm.

  References:
  - Erdős, P., "On a Diophantine equation", Mat. Lapok 1 (1950), 192-210
  - Mordell, L.J., "Diophantine Equations", Academic Press (1969)
  - Guy, R.K., "Unsolved Problems in Number Theory", Problem D11
  - Swett, A., computational verification up to 10^14
-/

import Mathlib

open Nat Filter

namespace Erdos242

/-! ## Egyptian Fraction Representation -/

/--
A representation of a/n as a sum of k unit fractions with distinct positive denominators.
-/
def IsEgyptianFractionRep (a n : ℕ) (k : ℕ) (denoms : Fin k → ℕ) : Prop :=
  (∀ i : Fin k, 0 < denoms i) ∧
  (∀ i j : Fin k, i < j → denoms i < denoms j) ∧
  (a : ℚ) / n = ∑ i : Fin k, (1 : ℚ) / (denoms i)

/-! ## The Erdős-Straus Conjecture -/

/--
**Erdős Problem #242** (Erdős-Straus Conjecture):

For every n > 2, the fraction 4/n can be expressed as a sum of exactly
three unit fractions with distinct positive denominators:

  4/n = 1/x + 1/y + 1/z  where 1 ≤ x < y < z

This is one of the most famous open problems in elementary number theory.
It has been verified computationally up to n = 10^17 but remains unproved.
-/
def ErdosStrausConjecture : Prop :=
  ∀ n : ℕ, 2 < n → ∃ x y z : ℕ,
    1 ≤ x ∧ x < y ∧ y < z ∧
    (4 : ℚ) / n = 1 / x + 1 / y + 1 / z

/-! ## Known Partial Results -/

/--
**Four fractions trivially suffice**: By the greedy algorithm, any a/n with a < n
can be written as a sum of at most n unit fractions.
-/
axiom four_fractions_suffice :
    ∀ n : ℕ, 2 < n → ∃ x y z w : ℕ,
      1 ≤ x ∧ x < y ∧ y < z ∧ z < w ∧
      (4 : ℚ) / n = 1 / x + 1 / y + 1 / z + 1 / w

/--
**Density result**: The Erdős-Straus conjecture holds for "almost all" n
in the sense of natural density. The set of exceptions has density 0.
-/
axiom erdos_straus_almost_all :
    ∃ S : Set ℕ, (∀ n ∈ S, 2 < n → ∃ x y z : ℕ,
      1 ≤ x ∧ x < y ∧ y < z ∧ (4 : ℚ) / n = 1 / x + 1 / y + 1 / z) ∧
    (∀ N : ℕ, (Finset.filter (· ∈ S) (Finset.range N)).card / N → 1)

/--
**Computational verification**: The conjecture has been verified for all
n ≤ 10^14 by various computational efforts.

We axiomatize a concrete upper bound.
-/
axiom computational_verification :
    ∀ n : ℕ, 2 < n → n ≤ 10^14 → ∃ x y z : ℕ,
      1 ≤ x ∧ x < y ∧ y < z ∧
      (4 : ℚ) / n = 1 / x + 1 / y + 1 / z

/-! ## Specific Cases -/

/--
**n ≡ 0 (mod 4)**: Easy case. If n = 4k, then 4/n = 1/k.
We can write 4/n = 1/(k+1) + 1/(k·(k+1)) + 1/(k·(k+1)·large) with care.
But more simply, for composite n the problem often has direct solutions.
-/
axiom mod_4_case :
    ∀ k : ℕ, 1 < k → ∃ x y z : ℕ,
      1 ≤ x ∧ x < y ∧ y < z ∧
      (4 : ℚ) / (4 * k) = 1 / x + 1 / y + 1 / z

/--
**n ≡ 1 (mod 4)**: Can be reduced using 4/n = 1/⌈n/4⌉ + (4k-n)/(n·⌈n/4⌉).
-/
axiom mod_4_equiv_1_case :
    ∀ k : ℕ, ∃ x y z : ℕ,
      1 ≤ x ∧ x < y ∧ y < z ∧
      (4 : ℚ) / (4 * k + 1) = 1 / x + 1 / y + 1 / z

/-! ## Schinzel's Generalization -/

/--
**Schinzel's Conjecture**: For any fixed a, the equation
  a/n = 1/x + 1/y + 1/z
has a solution in distinct positive integers for all sufficiently large n.

This is a generalization of Erdős-Straus (which is the case a = 4).
-/
def SchinzelConjecture : Prop :=
  ∀ a : ℕ, 0 < a → ∀ᶠ n in atTop, ∃ x y z : ℕ,
    1 ≤ x ∧ x < y ∧ y < z ∧
    (a : ℚ) / n = 1 / x + 1 / y + 1 / z

/--
Schinzel's conjecture generalizes Erdős-Straus.
-/
theorem schinzel_implies_erdos_straus_eventually :
    SchinzelConjecture → ∀ᶠ n in atTop, ∃ x y z : ℕ,
      1 ≤ x ∧ x < y ∧ y < z ∧
      (4 : ℚ) / n = 1 / x + 1 / y + 1 / z := by
  intro hSchinzel
  exact hSchinzel 4 (by norm_num)

/-! ## Concrete Examples -/

/--
**Example**: 4/3 = 1/1 + 1/3 + 0? No, we need three distinct denominators.
Let's check: 4/3 = 1/1 + 1/4 + 1/12? Check: 1 + 1/4 + 1/12 = 12/12 + 3/12 + 1/12 = 16/12 = 4/3. ✓
-/
theorem example_n_3 : (4 : ℚ) / 3 = 1 / 1 + 1 / 4 + 1 / 12 := by norm_num

/--
**Example**: 4/5 = 1/2 + 1/4 + 1/20?
Check: 10/20 + 5/20 + 1/20 = 16/20 = 4/5. ✓
-/
theorem example_n_5 : (4 : ℚ) / 5 = 1 / 2 + 1 / 4 + 1 / 20 := by norm_num

/--
**Example**: 4/7 = 1/2 + 1/14 + ?
We need 4/7 - 1/2 = 8/14 - 7/14 = 1/14. So 4/7 = 1/2 + 1/8 + 1/56?
Check: 1/2 + 1/8 + 1/56 = 28/56 + 7/56 + 1/56 = 36/56 = 9/14 ≠ 4/7.
Try: 4/7 = 1/2 + 1/15 + 1/210?
Check: 1/2 = 105/210, 1/15 = 14/210, 1/210 = 1/210. Sum = 120/210 = 4/7. ✓
-/
theorem example_n_7 : (4 : ℚ) / 7 = 1 / 2 + 1 / 15 + 1 / 210 := by norm_num

/-! ## Current Status -/

/--
**Summary**: The Erdős-Straus conjecture remains open:

| Statement | Status |
|-----------|--------|
| 4/n = 1/x + 1/y + 1/z for all n > 2 | OPEN |
| Verified for n ≤ 10^17 | COMPUTED |
| Holds for almost all n (density 1) | PROVED |
| 4 unit fractions suffice | TRIVIAL |

The problem's difficulty lies in the "distinct" requirement for denominators.
-/
axiom erdos_straus_open : ErdosStrausConjecture ∨ ¬ErdosStrausConjecture

/-! ## Summary -/

theorem summary_erdos_242 :
    (4 : ℚ) / 3 = 1 / 1 + 1 / 4 + 1 / 12 ∧
    (4 : ℚ) / 5 = 1 / 2 + 1 / 4 + 1 / 20 ∧
    (4 : ℚ) / 7 = 1 / 2 + 1 / 15 + 1 / 210 ∧
    (ErdosStrausConjecture ∨ ¬ErdosStrausConjecture) := by
  refine ⟨example_n_3, example_n_5, example_n_7, erdos_straus_open⟩

end Erdos242
