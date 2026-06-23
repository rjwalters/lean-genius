/-
  A₄ Has No Subgroup of Order 6

  The alternating group A₄ = alternatingGroup (Fin 4) has order 12.
  Although 6 divides 12, A₄ has NO subgroup of order 6.
  This is the canonical counterexample showing the converse of Lagrange's theorem fails.

  **Proof outline:**
  (1) |A₄| = 12 (native_decide).
  (2) Elements of A₄ have orders 1, 2, or 3 — no order-6 elements exist.
  (3) A direct finite enumeration (native_decide over all 2¹² subsets) shows
      no 6-element subset of A₄ satisfies the subgroup axioms.
  (4) This lifts to the Subgroup type via Fintype.card_subtype.

  **Alternative mathematical argument:**
  Any H ≤ A₄ with |H| = 6 has index 2, so H ⊴ A₄.
  The conjugacy classes of A₄ have sizes 1, 3, 4, 4 (total 12).
  A normal subgroup is a union of conjugacy classes.
  No subset of {1, 3, 4, 4} containing 1 sums to 6 — contradiction.

  References:
  - Herstein, "Topics in Algebra," Chapter 2
  - https://en.wikipedia.org/wiki/Alternating_group#Subgroups

  Tags: group-theory, lagrange, alternating-group, counterexample, finite-groups
-/

import Mathlib

open Subgroup Fintype

abbrev A4 : Type* := alternatingGroup (Fin 4)

namespace LagrangeOQ01OQ02

-- ============================================================
-- Part I: Basic facts about A₄
-- ============================================================

/-- A₄ has exactly 12 elements. -/
theorem A4_card : Fintype.card A4 = 12 := by native_decide

/-- Every element of A₄ has order 1, 2, or 3; no element has order 6.
    This rules out A₄ containing a cyclic subgroup Z₆. -/
theorem A4_no_element_order6 : ∀ x : A4, orderOf x ≠ 6 := by native_decide

/-- A₄ has exactly 3 elements of order 2 (the double transpositions). -/
theorem A4_three_order2_elements :
    (Finset.univ.filter (fun x : A4 => orderOf x = 2)).card = 3 := by native_decide

/-- A₄ has exactly 8 elements of order 3 (the 3-cycles). -/
theorem A4_eight_order3_elements :
    (Finset.univ.filter (fun x : A4 => orderOf x = 3)).card = 8 := by native_decide

-- ============================================================
-- Part II: No 6-element subgroup (finite enumeration)
-- ============================================================

/-- **Key lemma**: No 6-element subset of A₄ satisfies the subgroup axioms.

    Verified by exhaustive enumeration over all C(12,6) = 924 size-6 subsets
    of the 12-element group A₄. (native_decide checks all 2¹² = 4096 subsets.) -/
theorem A4_no_subgroup_order6_finset :
    ∀ S : Finset A4,
    S.card = 6 →
    (1 : A4) ∈ S →
    (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) →
    (∀ a ∈ S, a⁻¹ ∈ S) → False := by
  native_decide

-- ============================================================
-- Part III: Main theorem (Subgroup formulation)
-- ============================================================

/-- **Main theorem**: A₄ has no subgroup of order 6.

    This is the standard counterexample to the converse of Lagrange's theorem:
    6 | |A₄| = 12, yet no H ≤ A₄ satisfies |H| = 6. -/
theorem A4_no_subgroup_order6 (H : Subgroup A4) [Fintype H] :
    Fintype.card H ≠ 6 := by
  intro h6
  have hmem := @A4_no_subgroup_order6_finset (Finset.univ.filter (· ∈ H))
  apply hmem
  · -- Show (filter (· ∈ H) univ).card = 6
    have hcard : Fintype.card H = (Finset.univ.filter (· ∈ H)).card := by
      simp [Fintype.card_subtype]
    omega
  · -- 1 ∈ H
    simp [H.one_mem]
  · -- Closed under multiplication
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb ⊢
    exact H.mul_mem ha hb
  · -- Closed under inverses
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact H.inv_mem ha

-- ============================================================
-- Part IV: Corollaries
-- ============================================================

/-- A normal subgroup of A₄ of index 2 would have order 6 — which cannot exist. -/
theorem A4_no_index2_subgroup (H : Subgroup A4) [Fintype H] :
    H.index ≠ 2 := by
  intro hidx
  have hcard6 : Fintype.card H = 6 := by
    have hmul := H.card_mul_index
    have hA4 : Fintype.card A4 = 12 := A4_card
    rw [Nat.card_eq_fintype_card] at hmul
    rw [hA4] at hmul
    omega
  exact A4_no_subgroup_order6 H hcard6

/-- Lagrange's theorem does not reverse: 6 ∣ |A₄| but A₄ has no subgroup of order 6. -/
theorem lagrange_converse_fails :
    (6 : ℕ) ∣ Fintype.card A4 ∧
    ∀ (H : Subgroup A4) [Fintype H], Fintype.card H ≠ 6 :=
  ⟨⟨2, by simp [A4_card]⟩, fun H => A4_no_subgroup_order6 H⟩

end LagrangeOQ01OQ02
