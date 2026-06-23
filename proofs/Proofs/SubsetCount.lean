import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# The Number of Subsets of a Set

## What This Proves
A finite set with n elements has exactly 2^n subsets. This is Wiedijk's 100 Theorems #52.

$$|S| = n \implies |\mathcal{P}(S)| = 2^n$$

This fundamental result in combinatorics underlies many counting arguments and has deep
connections to binary representations: each subset corresponds to choosing "in or out"
for each element.

## Approach
- **Foundation (from Mathlib):** We use `Finset.card_powerset` which directly proves
  that the powerset of a Finset has cardinality 2^n.
- **Original Contributions:** Pedagogical wrapper theorems with explicit documentation
  explaining the bijection with binary strings.
- **Proof Techniques Demonstrated:** Working with Finset, powerset operations, and
  exponential cardinality bounds.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [x] Pedagogical examples
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Mathlib.Data.Finset.Powerset` : Powerset operations on finite sets
- `Finset.card_powerset` : Cardinality of powerset equals 2^n
- `Finset.powerset` : The powerset of a Finset as a Finset of Finsets

## Historical Note
This result has been known since antiquity and appears in many mathematical contexts.
The connection to binary representations makes it fundamental to computer science:
a set with n elements can represent 2^n different states.

## Why This Works
Each element of a set is either included or excluded from a subset. With n elements
and 2 choices per element, we get 2^n total possibilities. This bijection between
subsets and binary strings of length n is the core insight.

## Wiedijk's 100 Theorems: #52
-/

namespace SubsetCount

/-! ## The Main Theorem -/

/-- **Number of Subsets Theorem**: A finite set with n elements has exactly 2^n subsets.

    This is the fundamental counting result for powersets.

    The proof relies on the bijection between subsets and characteristic functions
    (or equivalently, binary strings): each element is either "in" (1) or "out" (0),
    giving 2 choices per element. -/
theorem card_powerset_eq_two_pow (s : Finset α) :
    s.powerset.card = 2 ^ s.card :=
  Finset.card_powerset s

/-- Alternative formulation: the number of subsets of a set with cardinality n is 2^n. -/
theorem subsets_count {s : Finset α} (h : s.card = n) :
    s.powerset.card = 2 ^ n := by
  rw [Finset.card_powerset, h]

/-! ## The Binary Bijection Intuition

The key insight is that subsets of {1, 2, ..., n} correspond bijectively to
binary strings of length n:

| Subset    | Binary String | Decimal |
|-----------|---------------|---------|
| {}        | 000...0       | 0       |
| {1}       | 100...0       | 1       |
| {2}       | 010...0       | 2       |
| {1,2}     | 110...0       | 3       |
| ...       | ...           | ...     |
| {1,...,n} | 111...1       | 2^n - 1 |

This gives exactly 2^n subsets, numbered 0 through 2^n - 1.
-/

/-! ## Examples and Verification -/

/-- The empty set has exactly one subset: itself. -/
example : (∅ : Finset ℕ).powerset.card = 1 := by
  simp [Finset.card_powerset]

/-- A singleton set has exactly 2 subsets: {} and {a}. -/
example (a : ℕ) : ({a} : Finset ℕ).powerset.card = 2 := by
  simp [Finset.card_powerset]

/-- A set with 3 distinct elements has 8 subsets. -/
example : ({1, 2, 3} : Finset ℕ).powerset.card = 8 := by native_decide

/-- A set with 4 distinct elements has 16 subsets. -/
example : ({1, 2, 3, 4} : Finset ℕ).powerset.card = 16 := by native_decide

/-! ## Properties of the Powerset -/

/-- The empty set is always in the powerset. -/
theorem empty_mem_powerset (s : Finset α) : ∅ ∈ s.powerset :=
  Finset.empty_mem_powerset s

/-- Every set is a subset of itself, so it's in its own powerset. -/
theorem self_mem_powerset (s : Finset α) : s ∈ s.powerset :=
  Finset.mem_powerset_self s

/-- Characterization: t is in the powerset of s iff t ⊆ s. -/
theorem mem_powerset_iff (s t : Finset α) : t ∈ s.powerset ↔ t ⊆ s :=
  Finset.mem_powerset

/-! ## Cardinality Bounds -/

/-- The powerset is never empty (it always contains at least the empty set). -/
theorem powerset_nonempty (s : Finset α) : s.powerset.Nonempty :=
  ⟨∅, empty_mem_powerset s⟩

/-- The powerset cardinality is always at least 1. -/
theorem card_powerset_pos (s : Finset α) : 0 < s.powerset.card := by
  rw [card_powerset_eq_two_pow]
  exact Nat.pos_pow_of_pos s.card (by norm_num : 0 < 2)

/-- Adding an element doubles the number of subsets. -/
theorem card_powerset_insert [DecidableEq α] (a : α) (s : Finset α) (ha : a ∉ s) :
    (insert a s).powerset.card = 2 * s.powerset.card := by
  rw [card_powerset_eq_two_pow, card_powerset_eq_two_pow]
  rw [Finset.card_insert_of_not_mem ha]
  ring

/-! ## Relationship to Subsets of Various Sizes

The powerset contains subsets of all possible sizes from 0 to n.
The number of k-element subsets is C(n,k), and we have:

$$\sum_{k=0}^{n} \binom{n}{k} = 2^n$$

This is a corollary of the binomial theorem with x = y = 1.
-/

/-- The sum of binomial coefficients equals 2^n (subset counting interpretation). -/
theorem sum_choose_eq_two_pow (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), n.choose k = 2 ^ n :=
  Nat.sum_range_choose n

/-! ## Connection to Fintype

For a Fintype (a type with finitely many elements), the cardinality
of the set of all subsets is 2^(cardinality of the type).
-/

/-- For a finite type, the number of Finsets equals 2^n where n is the type's size. -/
theorem fintype_card_finset (α : Type*) [Fintype α] :
    Fintype.card (Finset α) = 2 ^ Fintype.card α :=
  Fintype.card_finset

/-! ## Why 2^n? The Counting Argument

Each element can be:
- INCLUDED in a subset, or
- EXCLUDED from a subset

With n elements, each making an independent binary choice,
we have 2 × 2 × ... × 2 = 2^n possibilities.

This is the same as counting functions from an n-element set to {0, 1}.
-/

#check card_powerset_eq_two_pow
#check subsets_count
#check sum_choose_eq_two_pow
#check fintype_card_finset

end SubsetCount
