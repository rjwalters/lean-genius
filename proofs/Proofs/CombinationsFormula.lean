import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-!
# Formula for the Number of Combinations

## What This Proves
The number of ways to choose k elements from a set of n elements is:

$$C(n,k) = \binom{n}{k} = \frac{n!}{k!(n-k)!}$$

This fundamental formula in combinatorics counts the number of k-element subsets
of an n-element set.

## Approach
- **Foundation (from Mathlib):** We use `Nat.choose_eq_factorial_div_factorial` which
  directly proves the factorial formula for binomial coefficients.
- **Original Contributions:** Pedagogical wrapper theorems with explicit documentation
  explaining the combinatorial interpretation.
- **Proof Techniques Demonstrated:** Factorial manipulation, natural number division,
  combinatorial identities.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [x] Pedagogical examples
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Mathlib.Data.Nat.Choose.Basic` : Definition and properties of binomial coefficients
- `Mathlib.Data.Nat.Factorial.Basic` : Factorial function and properties
- `Nat.choose_eq_factorial_div_factorial` : The main factorial formula

## Historical Note
The binomial coefficient formula has been known for centuries. The notation C(n,k)
comes from "combinations", and the formula n!/(k!(n-k)!) was formalized as
mathematicians developed the theory of permutations and combinations. Pascal's
1654 treatise "Traité du triangle arithmétique" systematically explored these numbers.

## Why This Works
When selecting k items from n:
- There are n! ways to arrange all n items
- We divide by k! because the order of selected items doesn't matter
- We divide by (n-k)! because the order of unselected items doesn't matter

This gives n! / (k! × (n-k)!).

## Wiedijk's 100 Theorems: #58
-/

namespace CombinationsFormula

/-! ## The Main Theorem -/

/-- **Formula for Number of Combinations (Wiedijk #58)**

The number of ways to choose k elements from n elements is:
C(n,k) = n! / (k! × (n-k)!)

This is the fundamental formula for binomial coefficients, connecting
the combinatorial definition (counting subsets) to the factorial formula. -/
theorem combinations_formula (n k : ℕ) (h : k ≤ n) :
    Nat.choose n k = n.factorial / (k.factorial * (n - k).factorial) :=
  Nat.choose_eq_factorial_div_factorial h

/-- Alternative statement: the product of factorials divides n! exactly,
giving the binomial coefficient. -/
theorem factorial_product_divides (n k : ℕ) (h : k ≤ n) :
    k.factorial * (n - k).factorial ∣ n.factorial :=
  Nat.factorial_mul_factorial_dvd_factorial h

/-! ## Properties of Binomial Coefficients -/

/-- **Symmetry**: C(n,k) = C(n, n-k)

Choosing k items is the same as choosing which n-k items to leave out. -/
theorem choose_symmetry (n k : ℕ) (h : k ≤ n) :
    Nat.choose n k = Nat.choose n (n - k) :=
  (Nat.choose_symm h).symm

/-- **Boundary Case**: C(n, 0) = 1

There is exactly one way to choose nothing: the empty selection. -/
theorem choose_zero_right (n : ℕ) : Nat.choose n 0 = 1 :=
  Nat.choose_zero_right n

/-- **Boundary Case**: C(n, n) = 1

There is exactly one way to choose everything: take all elements. -/
theorem choose_self (n : ℕ) : Nat.choose n n = 1 :=
  Nat.choose_self n

/-- **Linear Case**: C(n, 1) = n

There are n ways to choose one element from n elements. -/
theorem choose_one_right (n : ℕ) : Nat.choose n 1 = n :=
  Nat.choose_one_right n

/-! ## Pascal's Triangle Relationship -/

/-- **Pascal's Identity**: C(n+1, k+1) = C(n, k) + C(n, k+1)

Each element in Pascal's triangle is the sum of the two elements above it.
This recurrence is fundamental to computing binomial coefficients. -/
theorem pascal_identity (n k : ℕ) :
    Nat.choose (n + 1) (k + 1) = Nat.choose n k + Nat.choose n (k + 1) :=
  Nat.choose_succ_succ n k

/-! ## The Factorial Interpretation

The formula n! / (k!(n-k)!) arises from the relationship between
permutations and combinations:

- P(n,k) = n! / (n-k)! counts ordered selections (permutations)
- C(n,k) = P(n,k) / k! removes the ordering, giving combinations

Thus: C(n,k) = n! / ((n-k)! × k!) = n! / (k! × (n-k)!)
-/

/-- **Falling Factorial Form**: C(n,k) equals the falling factorial divided by k!

The falling factorial n × (n-1) × ... × (n-k+1) counts ordered selections.
Dividing by k! removes the ordering. -/
theorem choose_eq_desc_factorial_div (n k : ℕ) :
    Nat.choose n k = Nat.descFactorial n k / k.factorial :=
  Nat.choose_eq_descFactorial_div_factorial n k

/-! ## Verification Examples -/

/-- C(5, 2) = 10 -/
example : Nat.choose 5 2 = 10 := by native_decide

/-- C(10, 3) = 120 -/
example : Nat.choose 10 3 = 120 := by native_decide

/-- C(6, 3) = 20 -/
example : Nat.choose 6 3 = 20 := by native_decide

/-- Verify: 5! / (2! × 3!) = 10 -/
example : Nat.factorial 5 / (Nat.factorial 2 * Nat.factorial 3) = 10 := by native_decide

/-- Verify: 10! / (3! × 7!) = 120 -/
example : Nat.factorial 10 / (Nat.factorial 3 * Nat.factorial 7) = 120 := by native_decide

/-- Symmetry example: C(7, 2) = C(7, 5) -/
example : Nat.choose 7 2 = Nat.choose 7 5 := by native_decide

/-- Pascal's identity example: C(5, 3) = C(4, 2) + C(4, 3) -/
example : Nat.choose 5 3 = Nat.choose 4 2 + Nat.choose 4 3 := by native_decide

/-! ## Connection to Subset Counting

C(n,k) also counts the number of k-element subsets of an n-element set.
This combinatorial interpretation is fundamental to probability theory
and many counting arguments. -/

/-- The number of k-element subsets of an n-element Finset is C(n,k). -/
theorem card_subsets_of_size (s : Finset α) (k : ℕ) :
    (Finset.powersetCard k s).card = Nat.choose s.card k :=
  Finset.card_powersetCard k s

#check combinations_formula
#check factorial_product_divides
#check choose_symmetry
#check pascal_identity

end CombinationsFormula
