import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Combinatorics.Derangements.Basic
import Mathlib.Tactic

/-!
# The Derangements Formula

## What This Proves
A derangement is a permutation with no fixed points. This is Wiedijk's 100 Theorems #88.

The number of derangements D(n) of n elements satisfies:

$$D_n = n! \sum_{k=0}^{n} \frac{(-1)^k}{k!}$$

With the recurrence relation: D(n) = (n-1)(D(n-1) + D(n-2))
And base cases: D(0) = 1, D(1) = 0.

The famous "hat-check problem": if n people check their hats and receive them back
randomly, D(n) is the number of ways no one gets their own hat back.

## Approach
- **Foundation (from Mathlib):** We use `Mathlib.Combinatorics.Derangements` which
  provides the definition and counting formulas for derangements.
- **Original Contributions:** Pedagogical wrapper theorems with the classical
  formulas, examples, and connection to the subfactorial notation.
- **Proof Techniques Demonstrated:** Working with permutations, fixed points,
  and alternating sums.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main results
- [x] Proves recurrence relation
- [x] Proves closed-form formula
- [x] Pedagogical examples
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Equiv.Perm.derangements` : Set of fixed-point-free permutations
- `Nat.numDerangements` : The function computing D(n)
- `card_derangements_eq_numDerangements` : Cardinality equals numDerangements
- `numDerangements_sum` : Closed-form sum formula

## Historical Note
The problem is also known as the "hat-check problem" or "problème des rencontres"
(problem of coincidences). Montmort studied it in 1708, and Euler later derived
the formula. The subfactorial notation !n was introduced by Whitworth in 1878.

As n → ∞, the probability of a random permutation being a derangement approaches 1/e.
This is approximately 36.79%, meaning about 63% of random permutations have at least
one fixed point.

## Wiedijk's 100 Theorems: #88
-/

namespace Derangements

open Finset Fintype Nat Equiv.Perm

/-! ## Core Definition -/

/-- A permutation is a derangement if it has no fixed points.
    That is, every element is moved by the permutation.

    Example: For {1,2,3}, the derangements are:
    - (1→2, 2→3, 3→1)  i.e. the 3-cycle (123)
    - (1→3, 2→1, 3→2)  i.e. the 3-cycle (132) -/
theorem mem_derangements_iff (f : Equiv.Perm α) :
    f ∈ derangements α ↔ ∀ x, f x ≠ x :=
  Iff.rfl

/-- Alternative characterization: a permutation is a derangement iff
    its set of fixed points is empty. -/
theorem derangement_iff_no_fixed_points (f : Equiv.Perm α) :
    f ∈ derangements α ↔ Function.fixedPoints f = ∅ :=
  mem_derangements_iff_fixedPoints_eq_empty

/-! ## The numDerangements Function

The number of derangements of n elements, denoted D(n) or !n.
This is defined recursively in Mathlib. -/

/-- Base case: D(0) = 1 (the unique empty permutation vacuously has no fixed points). -/
theorem numDerangements_zero : numDerangements 0 = 1 := rfl

/-- Base case: D(1) = 0 (a single element must map to itself). -/
theorem numDerangements_one : numDerangements 1 = 0 := rfl

/-! ## The Recurrence Relation -/

/-- **The Derangement Recurrence**: D(n+2) = (n+1) × (D(n) + D(n+1))

    This elegant recurrence has a combinatorial explanation:
    - Consider element 1 in a derangement of {1,...,n+2}
    - It must go somewhere, say to position k (n+1 choices)
    - Either k maps back to 1 (reducing to D(n)), or
    - k maps to something else (reducing to D(n+1)) -/
theorem derangements_recurrence (n : ℕ) :
    numDerangements (n + 2) = (n + 1) * (numDerangements n + numDerangements (n + 1)) :=
  numDerangements_add_two n

/-! ## The Closed-Form Formula -/

/-- **The Derangement Formula**: D(n) equals an alternating sum involving factorials.

    D(n) = n! × Σ(k=0 to n) (-1)^k / k!

    In Mathlib, this is expressed using ascending factorials:
    D(n) = Σ(k=0 to n) (-1)^k × (k+1)^{(n-k)}

    This formula comes from inclusion-exclusion. -/
theorem numDerangements_formula (n : ℕ) :
    (numDerangements n : ℤ) = ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * ↑((k + 1).ascFactorial (n - k)) :=
  numDerangements_sum n

/-! ## Cardinality Results -/

/-- The number of derangements of a finite type α equals numDerangements (card α).
    This connects the abstract definition with the computational function. -/
theorem card_derangements_eq [Fintype α] [DecidableEq α] :
    Fintype.card (derangements α) = numDerangements (Fintype.card α) :=
  card_derangements_eq_numDerangements α

/-- Derangements on Fin n have exactly numDerangements n elements. -/
theorem card_derangements_fin (n : ℕ) :
    Fintype.card (derangements (Fin n)) = numDerangements n := by
  rw [card_derangements_eq, Fintype.card_fin]

/-! ## Concrete Examples -/

/-- D(2) = 1: The only derangement of {1,2} is the swap (1→2, 2→1). -/
example : numDerangements 2 = 1 := by native_decide

/-- D(3) = 2: The derangements of {1,2,3} are the two 3-cycles. -/
example : numDerangements 3 = 2 := by native_decide

/-- D(4) = 9: There are 9 derangements of 4 elements. -/
example : numDerangements 4 = 9 := by native_decide

/-- D(5) = 44: There are 44 derangements of 5 elements. -/
example : numDerangements 5 = 44 := by native_decide

/-- D(6) = 265: There are 265 derangements of 6 elements. -/
example : numDerangements 6 = 265 := by native_decide

/-! ## The Hat-Check Problem

The classic formulation: n people check their hats at a restaurant. When leaving,
the hats are returned randomly. What's the probability no one gets their own hat?

Answer: D(n) / n!

As n → ∞, this approaches 1/e ≈ 0.3679.

For specific values:
- n=2: 1/2 = 50%
- n=3: 2/6 = 33.3%
- n=4: 9/24 = 37.5%
- n=5: 44/120 = 36.7%
- n=10: 1334961/3628800 ≈ 36.79%
-/

/-! ## Properties -/

/-- The identity permutation is never a derangement (for nonempty types). -/
theorem one_not_mem_derangements {α : Type*} [Nonempty α] :
    (1 : Equiv.Perm α) ∉ derangements α := by
  intro h
  have := h (Classical.arbitrary α)
  simp at this

/-- A derangement composed with itself may or may not be a derangement.
    For example, a 3-cycle squared is still a 3-cycle (derangement),
    but a transposition squared is the identity (not a derangement). -/
theorem derangement_mul_self_not_always_derangement :
    ∃ (f : Equiv.Perm (Fin 2)), f ∈ derangements (Fin 2) ∧ f * f ∉ derangements (Fin 2) := by
  use Equiv.swap 0 1
  constructor
  · intro x
    fin_cases x <;> simp [Equiv.swap_apply_of_ne_of_ne]
  · simp only [mem_derangements_iff, Equiv.Perm.coe_mul, Function.comp_apply, ne_eq,
      not_forall, not_not]
    use 0
    simp [Equiv.swap_apply_left]

/-! ## Subfactorial Notation

The number of derangements D(n) is also written as !n (subfactorial n).
The first few values are:

| n | !n = D(n) | n! | D(n)/n! |
|---|-----------|-----|---------|
| 0 | 1 | 1 | 1.000 |
| 1 | 0 | 1 | 0.000 |
| 2 | 1 | 2 | 0.500 |
| 3 | 2 | 6 | 0.333 |
| 4 | 9 | 24 | 0.375 |
| 5 | 44 | 120 | 0.367 |
| 6 | 265 | 720 | 0.368 |

The ratio converges to 1/e as n → ∞.
-/

/-! ## Inclusion-Exclusion Derivation

The formula D(n) = n! × Σ(-1)^k/k! comes from inclusion-exclusion:

Let Aᵢ = {permutations fixing element i}

D(n) = |complement of ⋃Aᵢ|
     = n! - |⋃Aᵢ|
     = n! - Σ|Aᵢ| + Σ|Aᵢ∩Aⱼ| - Σ|Aᵢ∩Aⱼ∩Aₖ| + ...

Since |Aᵢ₁ ∩ ... ∩ Aᵢₖ| = (n-k)! (fix k elements, permute the rest),
and there are C(n,k) ways to choose k elements:

D(n) = n! - C(n,1)(n-1)! + C(n,2)(n-2)! - C(n,3)(n-3)! + ...
     = Σₖ (-1)^k × C(n,k) × (n-k)!
     = Σₖ (-1)^k × n! / k!
     = n! × Σₖ (-1)^k / k!
-/

#check numDerangements
#check derangements_recurrence
#check numDerangements_formula
#check card_derangements_eq

end Derangements
