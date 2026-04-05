/-
# Distinct Submultiset Count Formula: ∏(mᵢ + 1)

OQ-01 follow-up to SubsetCountOQ02 (subset-count-multiset).

The parent proof showed |powerset(s)| = 2^n (counting with multiplicity).
This proof establishes the **distinct** count:

  |{t : Multiset α | t ≤ s}| = ∏ a ∈ s.toFinset, (s.count a + 1)

## Example

For s = {a, a, b} with count a = 2, count b = 1:
  distinct submultisets: {}, {a}, {a, a}, {b}, {a, b}, {a, a, b}
  count = 6 = (2+1)(1+1) = 3 × 2 ✓

## Proof Strategy

We establish a bijection:
  {t : Multiset α // t ≤ s}  ≃  ∀ a : ↑s.toFinset, Fin (s.count ↑a + 1)

- Forward: t ↦ (a ↦ t.count a)   [each count is bounded by s's count]
- Backward: f ↦ ∑ a : ↑s.toFinset, replicate (f a) a  [reconstruct from counts]

Then apply Fintype.card_pi and Finset.prod_coe_sort to get the product formula.

## Tags
combinatorics, multisets, counting, distinct-submultisets, powerset
-/

import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace SubsetCountMultisetOQ01

open Multiset BigOperators

variable {α : Type*} [DecidableEq α]

/-! ## Definitions -/

/-- The finset of distinct submultisets of s (each submultiset counted exactly once). -/
def distinctSubMultisets (s : Multiset α) : Finset (Multiset α) :=
  s.powerset.toFinset

/-- A multiset t is a distinct submultiset of s iff t ≤ s. -/
theorem mem_distinctSubMultisets {s t : Multiset α} :
    t ∈ distinctSubMultisets s ↔ t ≤ s := by
  simp [distinctSubMultisets, Multiset.mem_toFinset, Multiset.mem_powerset]

/-- The empty multiset has exactly one distinct submultiset: itself. -/
@[simp]
theorem distinctSubMultisets_empty :
    distinctSubMultisets (0 : Multiset α) = {0} := by
  simp [distinctSubMultisets, Multiset.powerset_zero]

/-- Every multiset is a distinct submultiset of itself. -/
theorem self_mem_distinctSubMultisets (s : Multiset α) :
    s ∈ distinctSubMultisets s :=
  mem_distinctSubMultisets.mpr le_rfl

/-! ## Key Helper Lemmas -/

/-- General: count distributes over Finset.sum of multisets. -/
private lemma count_finset_sum_distrib {ι : Type*} [DecidableEq ι] (F : Finset ι) (g : ι → Multiset α) (a : α) :
    (∑ b ∈ F, g b).count a = ∑ b ∈ F, (g b).count a := by
  induction F using Finset.induction_on with
  | empty => simp
  | @insert x rest hx ih =>
    rw [Finset.sum_insert hx, Multiset.count_add, ih, Finset.sum_insert hx]

/-- The count of an element in ∑ b : ↑s.toFinset, replicate (f b) ↑b equals f a. -/
private lemma count_finsetSum_replicate (s : Multiset α)
    (f : ∀ b : ↑s.toFinset, ℕ) (a : ↑s.toFinset) :
    (∑ b : ↑s.toFinset, Multiset.replicate (f b) (↑b : α)).count (↑a : α) = f a := by
  -- Distribute count over the finset sum
  rw [count_finset_sum_distrib]
  -- count of replicate: count a (replicate n b) = if a = b then n else 0
  simp only [Multiset.count_replicate]
  -- Rewrite: ↑b = ↑a ↔ b = a (coercion is injective on the subtype)
  have h_inj : ∀ b : ↑s.toFinset, ((↑b : α) = (↑a : α)) = (b = a) :=
    fun b => propext Subtype.val_inj
  simp_rw [h_inj]
  simp [Finset.sum_ite_eq']

/-- For a ∉ s.toFinset, the replicate sum has zero count at a. -/
private lemma count_finsetSum_replicate_not_mem (s : Multiset α)
    (f : ∀ b : ↑s.toFinset, ℕ) (a : α) (ha : a ∉ s.toFinset) :
    (∑ b : ↑s.toFinset, Multiset.replicate (f b) (↑b : α)).count a = 0 := by
  rw [count_finset_sum_distrib]
  simp only [Multiset.count_replicate]
  apply Finset.sum_eq_zero
  intro ⟨b, hb⟩ _
  simp only
  split_ifs with h
  · exact absurd (h ▸ hb) ha
  · rfl

/-- The replicate sum over s.toFinset is ≤ s. -/
private lemma finsetSum_replicate_le (s : Multiset α)
    (f : ∀ b : ↑s.toFinset, ℕ) (hf : ∀ b : ↑s.toFinset, f b ≤ s.count ↑b) :
    ∑ b : ↑s.toFinset, Multiset.replicate (f b) (↑b : α) ≤ s := by
  rw [Multiset.le_iff_count]
  intro a
  by_cases ha : a ∈ s.toFinset
  · rw [count_finsetSum_replicate s f ⟨a, ha⟩]
    exact hf ⟨a, ha⟩
  · rw [count_finsetSum_replicate_not_mem s f a ha]
    exact Nat.zero_le _

/-- A submultiset t ≤ s is uniquely reconstructed from its counts on s.toFinset. -/
private lemma submultiset_eq_finsetSum_replicate {s t : Multiset α} (ht : t ≤ s) :
    ∑ a : ↑s.toFinset, Multiset.replicate (t.count (↑a : α)) (↑a : α) = t := by
  ext a
  by_cases ha : a ∈ s.toFinset
  · rw [count_finsetSum_replicate s (fun b => t.count ↑b) ⟨a, ha⟩]
  · have h_zero : t.count a = 0 := by
      have h_le := (Multiset.le_iff_count.mp ht) a
      have h_s : s.count a = 0 := by
        rw [Multiset.count_eq_zero]
        rwa [Multiset.mem_toFinset] at ha
      omega
    rw [h_zero]
    rw [count_finsetSum_replicate_not_mem s (fun b => t.count ↑b) a ha]

/-! ## The Main Bijection -/

/-- The bijection between submultisets of s and count functions on distinct elements.
    Each submultiset t ≤ s corresponds to the function a ↦ t.count a. -/
def submultisetEquiv (s : Multiset α) :
    {t : Multiset α // t ≤ s} ≃ ∀ a : ↑s.toFinset, Fin (s.count ↑a + 1) where
  toFun := fun ⟨t, ht⟩ a =>
    ⟨t.count ↑a, Nat.lt_succ_of_le ((Multiset.le_iff_count.mp ht) ↑a)⟩
  invFun := fun f =>
    ⟨∑ a : ↑s.toFinset, Multiset.replicate (f a).val ↑a,
     finsetSum_replicate_le s (fun a => (f a).val)
       (fun a => Nat.lt_succ_iff.mp (f a).isLt)⟩
  left_inv := fun ⟨t, ht⟩ => by
    simp only [Subtype.mk.injEq]
    exact submultiset_eq_finsetSum_replicate ht
  right_inv := fun f => by
    ext ⟨a, ha⟩
    simp only [Fin.mk.injEq]
    rw [count_finsetSum_replicate s (fun b => (f b).val) ⟨a, ha⟩]

/-! ## Main Theorem -/

/-- **Distinct Submultiset Count Theorem**: The number of distinct submultisets of s
equals the product of (count a + 1) over all distinct elements a ∈ s.toFinset.

For example, for s = {a, a, b}: distinct submultisets = 6 = (2+1)(1+1) = 3 × 2. -/
theorem card_distinctSubMultisets (s : Multiset α) :
    (distinctSubMultisets s).card = s.toFinset.prod (fun a => s.count a + 1) := by
  -- Provide Fintype instances explicitly to avoid synthesis failures
  haveI instMem : Fintype {t : Multiset α // t ∈ distinctSubMultisets s} :=
    { elems := (distinctSubMultisets s).attach
      complete := fun ⟨t, ht⟩ => Finset.mem_attach _ ⟨t, ht⟩ }
  haveI instLE : Fintype {t : Multiset α // t ≤ s} :=
    Fintype.ofFinset (distinctSubMultisets s) fun t => mem_distinctSubMultisets
  -- Chain equalities via Fintype.card
  calc (distinctSubMultisets s).card
      = Fintype.card {t : Multiset α // t ∈ distinctSubMultisets s} :=
          (Fintype.card_coe (distinctSubMultisets s)).symm
    _ = Fintype.card {t : Multiset α // t ≤ s} :=
          Fintype.card_congr (Equiv.subtypeEquivRight fun t => mem_distinctSubMultisets)
    _ = Fintype.card (∀ a : ↑s.toFinset, Fin (s.count ↑a + 1)) :=
          Fintype.card_congr (submultisetEquiv s)
    _ = s.toFinset.prod (fun a => s.count a + 1) := by
          rw [Fintype.card_pi]
          simp_rw [Fintype.card_fin]
          exact Finset.prod_coe_sort s.toFinset (fun a => s.count a + 1)

/-! ## Corollaries and Examples -/

/-- For the empty multiset, there is exactly 1 distinct submultiset. -/
@[simp]
theorem card_distinctSubMultisets_empty :
    (distinctSubMultisets (0 : Multiset α)).card = 1 := by
  simp [distinctSubMultisets, Multiset.powerset_zero]

/-- For a singleton {a}, there are 2 distinct submultisets: {} and {a}. -/
theorem card_distinctSubMultisets_singleton (a : α) :
    (distinctSubMultisets ({a} : Multiset α)).card = 2 := by
  rw [card_distinctSubMultisets]
  simp [Multiset.toFinset_singleton, Finset.prod_singleton]

/-- {1, 1, 2} has (2+1)(1+1) = 6 distinct submultisets. -/
example : (distinctSubMultisets ({1, 1, 2} : Multiset ℕ)).card = 6 := by
  rw [card_distinctSubMultisets]; native_decide

/-- {1, 1, 1} has (3+1) = 4 distinct submultisets. -/
example : (distinctSubMultisets ({1, 1, 1} : Multiset ℕ)).card = 4 := by
  rw [card_distinctSubMultisets]; native_decide

/-- {1, 1, 2, 2, 2} has (2+1)(3+1) = 12 distinct submultisets. -/
example : (distinctSubMultisets ({1, 1, 2, 2, 2} : Multiset ℕ)).card = 12 := by
  rw [card_distinctSubMultisets]; native_decide

/-- {1, 2, 3, 4} (all distinct) has 2^4 = 16 distinct submultisets. -/
example : (distinctSubMultisets ({1, 2, 3, 4} : Multiset ℕ)).card = 16 := by
  rw [card_distinctSubMultisets]; native_decide

/-- For nodup multisets, the formula reduces to 2^n (matching the powerset count).
    When all counts are 1: ∏(1+1) = 2^n. -/
theorem nodup_card_eq_two_pow {s : Multiset α} (hn : s.Nodup) :
    (distinctSubMultisets s).card = 2 ^ s.card := by
  rw [card_distinctSubMultisets]
  -- Each element has count = 1
  have h_count : ∀ a ∈ s.toFinset, s.count a + 1 = 2 := by
    intro a ha
    rw [Multiset.mem_toFinset] at ha
    have h_le : s.count a ≤ 1 := Multiset.nodup_iff_count_le_one.mp hn a
    have h_pos : 0 < s.count a := Multiset.count_pos.mpr ha
    omega
  rw [Finset.prod_congr rfl h_count, Finset.prod_const]
  -- 2 ^ s.toFinset.card = 2 ^ s.card
  congr 1
  exact Multiset.toFinset_card_of_nodup hn

#check @card_distinctSubMultisets
#check @submultisetEquiv

end SubsetCountMultisetOQ01
