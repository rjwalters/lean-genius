import Mathlib

open Finset Function
open scoped Pointwise

namespace Erdos476OQ05Aristotle

variable {p : ℕ} [hp : Fact p.Prime]

/-
Cauchy-Davenport lower bound for erase+sumset: |(A\{a₀})+B| ≥ |A|+|B|-2 when |A|≥2, |B|≥1.
-/
lemma erase_add_card_ge (A B : Finset (ZMod p)) (a₀ : ZMod p) (ha₀ : a₀ ∈ A)
    (hA : 2 ≤ A.card) (hB : 1 ≤ B.card) (hlt : A.card + B.card - 1 < p) :
    A.card + B.card - 2 ≤ (A.erase a₀ + B).card := by
  -- By ZMod.cauchy_davenport:
  have h_cauchy_davenport : (p ⊓ (Finset.card (A.erase a₀) + Finset.card B - 1)) ≤ Finset.card ((A.erase a₀) + B) := by
    apply_rules [ ZMod.cauchy_davenport ];
    · exact hp.1;
    · exact Finset.card_pos.mp ( by rw [ Finset.card_erase_of_mem ha₀ ] ; omega );
    · exact Finset.card_pos.mp hB;
  grind +qlia

/-
Upper bound: |(A\{a₀})+B| ≤ |A+B|.
-/
lemma erase_add_card_le (A B : Finset (ZMod p)) (a₀ : ZMod p) :
    (A.erase a₀ + B).card ≤ (A + B).card := by
  exact Finset.card_le_card ( Finset.add_subset_add_right ( Finset.erase_subset _ _ ) )

/-
If some b₀ ∈ B is "non-redundant" (removing it decreases the sumset),
    then the new element gives a non-redundant a₀ ∈ A.
-/
lemma non_redundant_b_gives_a (A B : Finset (ZMod p)) (b₀ : ZMod p) (hb₀ : b₀ ∈ B)
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card)
    (h : (A + B).card = A.card + B.card - 1)
    (hlt : A.card + B.card < p)
    (hcard : (A + B.erase b₀).card = A.card + B.card - 2) :
    ∃ a₀ ∈ A, ((A.erase a₀) + B).card = A.card + B.card - 2 := by
  -- Since A + B = (A + B.erase b₀) ∪ (A + {b₀}) and the sets differ by 1 in cardinality, there is exactly 1 element y in (A + {b₀}) \ (A + B.erase b₀).
  obtain ⟨y, hy⟩ : ∃ y ∈ A + {b₀}, y ∉ A + B.erase b₀ := by
    contrapose! h;
    have h_subset : A + B ⊆ A + B.erase b₀ := by
      simp_all +decide [ Finset.subset_iff, Finset.mem_add ];
      grind;
    exact ne_of_lt ( lt_of_le_of_lt ( Finset.card_le_card h_subset ) ( by omega ) );
  -- Let $a₀$ be such that $y = a₀ + b₀$.
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ ∈ A, y = a₀ + b₀ := by
    rw [ Finset.mem_add ] at hy ; aesop;
  -- So y ∉ (A.erase a₀) + B, meaning (A.erase a₀) + B ⊊ A + B.
  have h_strict_subset : (A.erase a₀ + B) ⊂ A + B := by
    simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
    simp_all +decide [ Finset.mem_add ];
    grind;
  -- Since (A.erase a₀) + B ⊆ A + B and y ∉ (A.erase a₀) + B:
  have h_card_le : (A.erase a₀ + B).card ≤ (A + B).card - 1 := by
    exact Nat.le_sub_one_of_lt ( Finset.card_lt_card h_strict_subset );
  exact ⟨ a₀, ha₀.1, le_antisymm ( by omega ) ( by have := erase_add_card_ge A B a₀ ha₀.1 hA ( by linarith ) ( by omega ) ; omega ) ⟩

/-
In the all-redundant case, the counting argument gives (|A|-2)(|B|-2) ≥ 2,
    which is false for |B| = 2.
-/
lemma all_redundant_contradiction_B2 (A B : Finset (ZMod p))
    (hA3 : 2 < A.card) (hB : B.card = 2)
    (h : (A + B).card = A.card + B.card - 1)
    (hlt : A.card + B.card < p)
    (hredundant : ∀ b₀ ∈ B, (A + B.erase b₀).card = A.card + B.card - 1) :
    False := by
  obtain ⟨ b₁, b₂, hb₁, hb₂, hne ⟩ := Finset.card_eq_two.mp hB;
  simp_all +decide [ Finset.sum_add_distrib ]

end Erdos476OQ05Aristotle