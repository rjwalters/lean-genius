import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-
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

/- ## The Main Theorem -/

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

/- ## Properties of Binomial Coefficients -/

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

/- ## Pascal's Triangle Relationship -/

/-- **Pascal's Identity**: C(n+1, k+1) = C(n, k) + C(n, k+1)

Each element in Pascal's triangle is the sum of the two elements above it.
This recurrence is fundamental to computing binomial coefficients. -/
theorem pascal_identity (n k : ℕ) :
    Nat.choose (n + 1) (k + 1) = Nat.choose n k + Nat.choose n (k + 1) :=
  Nat.choose_succ_succ n k

/- ## The Factorial Interpretation

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

/- ## Verification Examples -/

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

/- ## Connection to Subset Counting

C(n,k) also counts the number of k-element subsets of an n-element set.
This combinatorial interpretation is fundamental to probability theory
and many counting arguments. -/

/-- The number of k-element subsets of an n-element Finset is C(n,k). -/
theorem card_subsets_of_size (s : Finset α) (k : ℕ) :
    (Finset.powersetCard k s).card = Nat.choose s.card k :=
  Finset.card_powersetCard k s

/- ## Part VII: Generalized Binomial Coefficients

The standard binomial coefficient C(n,k) requires n ∈ ℕ. The generalized binomial
coefficient extends this to any real (or complex) argument α:

  C(α, k) = α(α-1)(α-2)...(α-k+1) / k!

This is the "falling factorial" of α divided by k!. When α is a natural number,
this agrees with the standard definition.
-/

/-- The generalized binomial coefficient for real arguments.
    genBinom α k = α(α-1)(α-2)...(α-k+1) / k!

    This extends C(n,k) to non-integer α. -/
noncomputable def genBinom (α : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => genBinom α k * (α - k) / (k + 1)

/-- C(α, 0) = 1 for any α. -/
theorem genBinom_zero (α : ℝ) : genBinom α 0 = 1 := rfl

/-- The recursion for generalized binomial coefficients. -/
theorem genBinom_succ (α : ℝ) (k : ℕ) :
    genBinom α (k + 1) = genBinom α k * (α - k) / (k + 1) := rfl

/-- C(α, 1) = α for any α. -/
theorem genBinom_one (α : ℝ) : genBinom α 1 = α := by
  simp [genBinom]

/-- C(0, k) = 0 for k ≥ 1. -/
theorem genBinom_zero_pos (k : ℕ) (hk : k ≥ 1) : genBinom 0 k = 0 := by
  induction k with
  | zero => omega
  | succ n ih =>
    simp only [genBinom]
    rcases n with _ | m
    · simp
    · have : genBinom 0 (m + 1) = 0 := ih (by omega)
      simp [this]

/-- C(α, 2) = α(α-1)/2. -/
theorem genBinom_two (α : ℝ) : genBinom α 2 = α * (α - 1) / 2 := by
  simp [genBinom]; ring

/-- When α = n (a natural number) and k = 0, genBinom agrees with choose. -/
theorem genBinom_nat_zero (n : ℕ) : genBinom (n : ℝ) 0 = (Nat.choose n 0 : ℝ) := by
  simp [genBinom]

/-- Concrete verification: genBinom 5 2 = 10. -/
example : genBinom 5 2 = (10 : ℝ) := by
  simp [genBinom]; ring

/-- Concrete verification: genBinom 5 3 = 10. -/
example : genBinom 5 3 = (10 : ℝ) := by
  simp [genBinom]; ring

/-- Concrete verification: genBinom 10 3 = 120. -/
example : genBinom 10 3 = (120 : ℝ) := by
  simp [genBinom]; ring

/-- Concrete example: C(1/2, 2) = -1/8. -/
example : genBinom (1/2 : ℝ) 2 = -1/8 := by
  rw [genBinom_two]; ring

/-- Concrete example: C(-1, 3) = -1. -/
example : genBinom (-1 : ℝ) 3 = -1 := by
  simp [genBinom]; ring

/-
## Part VIII: Falling Product Representation

The generalized binomial coefficient can be expressed as a falling product
divided by factorial:
  genBinom α k = α(α-1)...(α-k+1) / k!

We define the falling product and prove this equivalence.
-/

/-- The falling product: α(α-1)(α-2)...(α-k+1).
    For natural number α = n, this is the descending factorial n!/(n-k)!. -/
noncomputable def fallingProd (α : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => fallingProd α k * (α - k)

/-- fallingProd α 0 = 1. -/
@[simp] theorem fallingProd_zero (α : ℝ) : fallingProd α 0 = 1 := rfl

/-- Recursion for fallingProd. -/
theorem fallingProd_succ (α : ℝ) (k : ℕ) :
    fallingProd α (k + 1) = fallingProd α k * (α - k) := rfl

/-- genBinom α k = fallingProd α k / k! -/
theorem genBinom_eq_fallingProd_div (α : ℝ) (k : ℕ) :
    genBinom α k = fallingProd α k / (k.factorial : ℝ) := by
  induction k with
  | zero => simp [genBinom, fallingProd]
  | succ n ih =>
    rw [genBinom_succ, ih, fallingProd_succ, Nat.factorial_succ, Nat.cast_mul]
    have hfact : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
    push_cast; ring

/-
## Part IX: Agreement with Natural Number Binomial Coefficients

The crucial consistency theorem: when α is a natural number n,
genBinom n k = C(n, k). This validates the generalization.
-/

/-- For natural n, the falling product equals the descending factorial. -/
theorem fallingProd_nat (n k : ℕ) :
    fallingProd (n : ℝ) k = (Nat.descFactorial n k : ℝ) := by
  induction k with
  | zero => simp [fallingProd, Nat.descFactorial_zero]
  | succ m ih =>
    rw [fallingProd_succ, ih, Nat.descFactorial_succ, Nat.cast_mul]
    -- Goal: ↑(descFactorial n m) * (↑n - ↑m) = ↑(n - m) * ↑(descFactorial n m)
    by_cases hle : m ≤ n
    · -- When m ≤ n: ℕ subtraction n - m agrees with ℝ subtraction
      rw [Nat.cast_sub hle]; ring
    · -- When m > n: n - m = 0 in ℕ, and descFactorial n m = 0
      push_neg at hle
      have h1 : Nat.descFactorial n m = 0 :=
        Nat.descFactorial_eq_zero_iff_lt.mpr hle
      simp [h1]

/-- **Consistency Theorem**: genBinom (↑n) k = ↑(Nat.choose n k) for all n, k : ℕ.

    This is the key theorem validating the generalization: when applied to
    natural numbers, the generalized binomial coefficient agrees with the
    classical one. -/
theorem genBinom_nat_eq_choose (n k : ℕ) :
    genBinom (n : ℝ) k = (Nat.choose n k : ℝ) := by
  rw [genBinom_eq_fallingProd_div, fallingProd_nat]
  rw [Nat.choose_eq_descFactorial_div_factorial]
  rw [Nat.cast_div (Nat.factorial_dvd_descFactorial n k)
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))]

/-
## Part X: Falling Product Identities
-/

/-- Key identity: fallingProd α (k+1) = α * fallingProd (α-1) k.
    The falling product of k+1 terms starting from α equals α times
    the falling product of k terms starting from α-1. -/
theorem fallingProd_succ_eq_mul (α : ℝ) (k : ℕ) :
    fallingProd α (k + 1) = α * fallingProd (α - 1) k := by
  induction k with
  | zero => simp [fallingProd]
  | succ n ih =>
    rw [fallingProd_succ, ih, fallingProd_succ]
    push_cast; ring

/-
## Part XI: The Negation Formula

A key identity for generalized binomial coefficients:
  C(-α, k) = (-1)^k * C(α + k - 1, k)

This "upper negation" formula connects negative arguments to positive ones.
-/

/-- fallingProd under negation: fallingProd (-α) k = (-1)^k * fallingProd (α + k - 1) k. -/
theorem fallingProd_neg (α : ℝ) (k : ℕ) :
    fallingProd (-α) k = (-1) ^ k * fallingProd (α + ↑k - 1) k := by
  induction k with
  | zero => simp [fallingProd]
  | succ n ih =>
    rw [fallingProd_succ, ih, pow_succ]
    -- RHS target: (-1) * (-1) ^ n * fallingProd (α + ↑(n + 1) - 1) (n + 1)
    -- = -(-1)^n * fallingProd (α + n) (n+1)
    -- Use fallingProd_succ_eq_mul: fallingProd (α + n) (n+1) = (α + n) * fallingProd (α + n - 1) n
    rw [fallingProd_succ_eq_mul (α + ↑(n + 1) - 1)]
    -- Now: (-1)^n * fallingProd (α + n - 1) n * (-α - n)
    --    = -(-1)^n * ((α + n + 1 - 1) * fallingProd (α + n + 1 - 1 - 1) n)
    --    = -(-1)^n * ((α + n) * fallingProd (α + n - 1) n)
    push_cast; ring

/-- **Upper Negation Formula**: C(-α, k) = (-1)^k * C(α + k - 1, k).

    This fundamental identity lets us compute C(-α, k) in terms of a
    positive-argument binomial coefficient. -/
theorem genBinom_neg (α : ℝ) (k : ℕ) :
    genBinom (-α) k = (-1) ^ k * genBinom (α + ↑k - 1) k := by
  rw [genBinom_eq_fallingProd_div, genBinom_eq_fallingProd_div, fallingProd_neg]
  ring

/-- Special case: C(-1, k) = (-1)^k for all k. -/
theorem genBinom_neg_one (k : ℕ) : genBinom (-1 : ℝ) k = (-1) ^ k := by
  rw [genBinom_neg]
  suffices h : genBinom (↑k : ℝ) k = 1 by
    simp [h]
  rw [genBinom_nat_eq_choose, Nat.choose_self, Nat.cast_one]

/-- Special case: C(-n, k) = (-1)^k * C(n+k-1, k) for natural n, when n+k ≥ 1. -/
theorem genBinom_neg_nat (n k : ℕ) (h : 1 ≤ n + k) :
    genBinom (-(n : ℝ)) k = (-1) ^ k * (Nat.choose (n + k - 1) k : ℝ) := by
  rw [genBinom_neg]
  congr 1
  -- Show ↑n + ↑k - 1 = ↑(n + k - 1)
  conv_lhs => rw [show (↑n : ℝ) + ↑k - 1 = ↑(n + k - 1 : ℕ) from by
    rw [Nat.cast_sub h]; push_cast; ring]
  exact genBinom_nat_eq_choose (n + k - 1) k

/-
## Part XII: Additional Identities
-/

/-- **Absorption Identity**: (k+1) * C(α, k+1) = α * C(α-1, k).

    This identity connects adjacent binomial coefficients and
    is useful in many combinatorial arguments. -/
theorem genBinom_absorption (α : ℝ) (k : ℕ) :
    (k + 1 : ℝ) * genBinom α (k + 1) = α * genBinom (α - 1) k := by
  rw [genBinom_eq_fallingProd_div, genBinom_eq_fallingProd_div]
  rw [Nat.factorial_succ, Nat.cast_mul]
  have hfact : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  rw [fallingProd_succ_eq_mul]
  push_cast; ring

/-- Concrete verification: genBinom (-1/2) 3 = -5/16. -/
example : genBinom (-1/2 : ℝ) 3 = -5/16 := by
  simp [genBinom]; ring

/-- Concrete verification: genBinom 4 3 = C(4,3) = 4. -/
example : genBinom (4 : ℝ) 3 = 4 := by
  simp [genBinom]; ring

/-- Concrete verification of negation: C(-3, 2) = (-1)^2 * C(4, 2) = 6. -/
example : genBinom (-3 : ℝ) 2 = 6 := by
  simp [genBinom]; ring

end CombinationsFormula
