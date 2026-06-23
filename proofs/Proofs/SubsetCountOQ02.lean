import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Multiset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-
# Subset Counting for Multisets

## What This Proves
Generalizes the subset counting theorem (|P(S)| = 2^n) to multisets.

For a multiset s with n elements (counted with multiplicity), the powerset
(all submultisets, counted with multiplicity) has cardinality 2^n.
Additionally, submultisets of fixed size k are counted by the binomial
coefficient C(n, k).

## Connection to Parent Proof
The parent proof (SubsetCount.lean) shows |P(S)| = 2^n for finite sets.
A set is a multiset where every element has multiplicity 1. The multiset
generalization shows the same formula holds when elements can repeat,
with n = total number of elements (with multiplicity).

## Key Difference: Sets vs Multisets
- For sets: each element is either in or out of a subset (2 choices per element)
- For multisets: choosing submultisets with multiplicity still gives 2^n total,
  because each occurrence of an element is independently in or out
- The number of DISTINCT submultisets is product(m_i + 1) over distinct elements,
  where m_i is the multiplicity of element i

## Mathlib Dependencies
- `Multiset.card_powerset` : card (powerset s) = 2 ^ card s
- `Multiset.card_powersetCard` : card (powersetCard n s) = (card s).choose n
-/

namespace SubsetCountMultiset

open Multiset

/-! ## Part I: Multiset Powerset Cardinality -/

/-- **Multiset Powerset Theorem**: A multiset with n elements (counted with
multiplicity) has 2^n submultisets (counted with multiplicity).

This generalizes the set version: when every element has multiplicity 1,
this reduces to the standard |P(S)| = 2^n. -/
theorem multiset_powerset_card {α : Type*} (s : Multiset α) :
    Multiset.card (Multiset.powerset s) = 2 ^ Multiset.card s :=
  Multiset.card_powerset s

/-- For the empty multiset, the powerset has exactly one element (the empty multiset). -/
theorem powerset_empty_card {α : Type*} :
    Multiset.card (Multiset.powerset (0 : Multiset α)) = 1 := by
  simp [Multiset.card_powerset]

/-- Adding an element doubles the powerset size. -/
theorem powerset_cons_card {α : Type*} (a : α) (s : Multiset α) :
    Multiset.card (Multiset.powerset (a ::ₘ s)) =
      2 * Multiset.card (Multiset.powerset s) := by
  simp [Multiset.card_powerset, pow_succ, mul_comm]

/-! ## Part II: Fixed-Size Submultisets -/

/-- **Multiset Choose Theorem**: The number of submultisets of size k from a
multiset of size n is C(n, k), the binomial coefficient.

This generalizes the set version: the number of k-element subsets of an
n-element set is C(n, k). For multisets, we count k-element submultisets
(with multiplicity in the counting). -/
theorem multiset_choose_card {α : Type*} (s : Multiset α) (k : ℕ) :
    Multiset.card (Multiset.powersetCard k s) = (Multiset.card s).choose k :=
  Multiset.card_powersetCard k s

/-- No submultisets of size > n exist. -/
theorem powersetCard_empty_of_lt {α : Type*} (s : Multiset α) (k : ℕ)
    (hk : Multiset.card s < k) :
    Multiset.powersetCard k s = 0 := by
  rw [eq_zero_iff_forall_not_mem]
  intro t ht
  rw [Multiset.mem_powersetCard] at ht
  have := Multiset.card_le_card ht.1
  omega

/-! ## Part III: Connection to Set Case -/

/-- For Finsets (sets without duplicates), the multiset powerset formula
agrees with the set powerset formula. -/
theorem finset_powerset_via_multiset {α : Type*} [DecidableEq α] (s : Finset α) :
    Multiset.card (Multiset.powerset s.val) = 2 ^ s.card := by
  rw [Multiset.card_powerset, Finset.card]

/-- Membership in the multiset powerset characterizes submultisets. -/
theorem mem_powerset_iff {α : Type*} (s t : Multiset α) :
    t ∈ Multiset.powerset s ↔ t ≤ s :=
  Multiset.mem_powerset

/-! ## Part IV: Concrete Examples -/

/-- The empty multiset has exactly 1 submultiset: itself. 2^0 = 1. -/
example : Multiset.card (Multiset.powerset (0 : Multiset ℕ)) = 1 := by
  simp [Multiset.card_powerset]

/-- A singleton multiset {a} has 2 submultisets: {} and {a}. 2^1 = 2. -/
example : Multiset.card (Multiset.powerset ({3} : Multiset ℕ)) = 2 := by
  simp [Multiset.card_powerset]

/-- A multiset with 3 elements has 8 submultisets. 2^3 = 8.
    Note: this counts with multiplicity. For {a, a, b}, the 8 submultisets
    include {a} counted twice (once for each copy of a). -/
example : Multiset.card (Multiset.powerset ({1, 1, 2} : Multiset ℕ)) = 8 := by
  simp [Multiset.card_powerset]

/-- C(4, 2) = 6: a 4-element multiset has 6 submultisets of size 2. -/
example : Multiset.card (Multiset.powersetCard 2 ({1, 2, 3, 4} : Multiset ℕ)) = 6 := by
  simp [Multiset.card_powersetCard]

#check @multiset_powerset_card
#check @multiset_choose_card
#check @finset_powerset_via_multiset

end SubsetCountMultiset
