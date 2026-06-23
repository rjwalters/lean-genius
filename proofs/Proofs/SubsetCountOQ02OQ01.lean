import Mathlib

/-!
# Distinct Submultiset Count: ∏(mᵢ + 1) (OQ-02-OQ-01)

## Open Question

Can the formula
  |{distinct submultisets of s}| = ∏ a ∈ s.toFinset, (s.count a + 1)
be formalized in Lean using Mathlib's `Multiset.toFinset` and multiplicity counting?

## Answer: YES — via `Multiset.card_Iic`

Mathlib contains this theorem in `Mathlib.Data.Multiset.Interval`:

```lean
theorem Multiset.card_Iic [DecidableEq α] (s : Multiset α) :
    (Finset.Iic s).card = ∏ i ∈ s.toFinset, (s.count i + 1)
```

`Finset.Iic s` = `{t : Multiset α | t ≤ s}` is the finset of all distinct submultisets.
The formula counts them as a product: for each distinct element `a` with multiplicity
`m = s.count a`, there are `m+1` choices (include 0, 1, ..., m copies).

## Mathematical Context

This generalizes the set case: for a nodup multiset (all counts = 1), the formula gives
`∏ a, 2 = 2^n`. The implementation in Mathlib proceeds via `DFinsupp.card_Icc` and the
isomorphism between `Multiset` and finitely-supported functions.

## Summary Statistics

- Sorries: 0
- Axioms: 0
- Key Mathlib theorem: `Multiset.card_Iic`
-/

namespace SubsetCountDistinct

open Multiset Finset

-- ============================================================================
-- Part I: The Main Theorem
-- ============================================================================

/-- **Distinct Submultiset Count**:
    A multiset `s` has exactly `∏ a ∈ s.toFinset, (s.count a + 1)` distinct submultisets.

    For each distinct element `a` with multiplicity `m`, a submultiset can include
    `0, 1, ..., m` copies of `a`. Since choices are independent, the total is ∏(mᵢ + 1).

    Proved directly by `Multiset.card_Iic`. -/
theorem distinct_submultisets_count [DecidableEq α] (s : Multiset α) :
    (Finset.Iic s).card = ∏ a ∈ s.toFinset, (s.count a + 1) :=
  Multiset.card_Iic s

-- ============================================================================
-- Part II: Fundamental Instances
-- ============================================================================

/-- The empty multiset has exactly 1 submultiset: the empty multiset itself. -/
theorem distinct_submultisets_empty [DecidableEq α] :
    (Finset.Iic (0 : Multiset α)).card = 1 := by
  simp [Multiset.card_Iic]

/-- A singleton `{a}` has exactly 2 distinct submultisets: `{}` and `{a}`. -/
theorem distinct_submultisets_singleton [DecidableEq α] (a : α) :
    (Finset.Iic ({a} : Multiset α)).card = 2 := by
  simp [Multiset.card_Iic]

/-- `{a, a, ..., a}` (n+1 copies) has exactly `n+2` distinct submultisets:
    `{}, {a}, {a,a}, ..., {a,...,a}` (with 0, 1, ..., n+1 copies). -/
theorem distinct_submultisets_replicate [DecidableEq α] (a : α) (n : ℕ) :
    (Finset.Iic (Multiset.replicate (n + 1) a)).card = n + 2 := by
  simp [Multiset.card_Iic, Multiset.toFinset_replicate, Multiset.count_replicate]

-- ============================================================================
-- Part III: Set Case
-- ============================================================================

/-- **Connection to the set case**: For a nodup multiset (all elements distinct),
    the distinct submultiset count equals `2^(card s)`. -/
theorem distinct_submultisets_nodup [DecidableEq α] (s : Multiset α) (hnd : s.Nodup) :
    (Finset.Iic s).card = 2 ^ s.card := by
  rw [Multiset.card_Iic]
  have h_count : ∀ a ∈ s.toFinset, s.count a + 1 = 2 := by
    intro a ha
    rw [Multiset.mem_toFinset] at ha
    have h_le : s.count a ≤ 1 := Multiset.nodup_iff_count_le_one.mp hnd a
    have h_pos : 0 < s.count a := Multiset.count_pos.mpr ha
    omega
  rw [Finset.prod_congr rfl h_count, Finset.prod_const]
  congr 1
  exact Multiset.toFinset_card_of_nodup hnd

-- ============================================================================
-- Part IV: Concrete Verifications
-- ============================================================================

/-- {0, 0, 1} as a multiset: count 0 = 2, count 1 = 1.
    Distinct submultisets: (2+1)(1+1) = 6. -/
theorem distinct_submultisets_ex1 :
    (Finset.Iic ({0, 0, 1} : Multiset ℕ)).card = 6 := by
  native_decide

/-- {0, 1, 2}: all distinct, so 2³ = 8. -/
theorem distinct_submultisets_ex2 :
    (Finset.Iic ({0, 1, 2} : Multiset ℕ)).card = 8 := by
  native_decide

/-- {0, 0, 0}: count 0 = 3, so (3+1) = 4. -/
theorem distinct_submultisets_ex3 :
    (Finset.Iic ({0, 0, 0} : Multiset ℕ)).card = 4 := by
  native_decide

/-- {0, 0, 1, 1, 2}: count 0 = 2, count 1 = 2, count 2 = 1.
    Distinct submultisets: (2+1)(2+1)(1+1) = 18. -/
theorem distinct_submultisets_ex4 :
    (Finset.Iic ({0, 0, 1, 1, 2} : Multiset ℕ)).card = 18 := by
  native_decide

-- ============================================================================
-- Part V: Multiplicativity
-- ============================================================================

/-- The distinct submultiset count is multiplicative: if `s` and `t` have disjoint
    support, then the count of `s + t` is the product of the individual counts. -/
theorem distinct_submultisets_disjoint [DecidableEq α] (s t : Multiset α)
    (hdisj : Disjoint s.toFinset t.toFinset) :
    (Finset.Iic (s + t)).card =
      (Finset.Iic s).card * (Finset.Iic t).card := by
  simp only [distinct_submultisets_count]
  -- (s + t).toFinset = s.toFinset ∪ t.toFinset
  have hst : (s + t).toFinset = s.toFinset ∪ t.toFinset := by
    ext a; simp [Multiset.mem_toFinset, Multiset.mem_add]
  rw [hst, Finset.prod_union hdisj]
  congr 1
  · apply Finset.prod_congr rfl
    intro a ha
    -- a ∈ s.toFinset and Disjoint s.toFinset t.toFinset → a ∉ t
    have hat : a ∉ t := fun hmem =>
      Finset.disjoint_left.mp hdisj ha (Multiset.mem_toFinset.mpr hmem)
    rw [Multiset.count_add, Multiset.count_eq_zero.mpr hat]
  · apply Finset.prod_congr rfl
    intro a ha
    -- a ∈ t.toFinset and Disjoint s.toFinset t.toFinset → a ∉ s
    have has : a ∉ s := fun hmem =>
      Finset.disjoint_left.mp (Finset.disjoint_comm.mp hdisj) ha (Multiset.mem_toFinset.mpr hmem)
    rw [Multiset.count_add, Multiset.count_eq_zero.mpr has, zero_add]

-- ============================================================================
-- Summary Check
-- ============================================================================

#check @distinct_submultisets_count
#check @distinct_submultisets_nodup
#check @distinct_submultisets_disjoint

end SubsetCountDistinct
