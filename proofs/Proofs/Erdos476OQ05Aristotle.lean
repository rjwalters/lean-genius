import Mathlib

open Finset Function
open scoped Pointwise

namespace Erdos476OQ05Aristotle

variable {p : ℕ} [hp : Fact p.Prime]

/-
An arithmetic progression in ZMod p starting at `a` with difference `d`.
Mirroring the definition from Erdos476OQ05Problem.
-/
def IsArithmeticProgression (A : Finset (ZMod p)) (a d : ZMod p) : Prop :=
  A = (Finset.range A.card).image (fun (i : ℕ) => a + (i : ZMod p) * d)

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

/-
**Position Analysis**: When AP₁ (start s₁, length n, diff d) and AP₂ (start s₂, length m, diff d)
satisfy (AP₁ \ AP₂).card = 1 with n ≤ m and n + m ≤ p, then:
  s₁ = s₂ - d  (AP₁ "predecessor" of AP₂, the unique missing element is the first of AP₁)
  OR
  s₁ = s₂ + (m - n + 1) * d  (AP₁ "successor" of AP₂, the unique missing element is the last of AP₁)

This is used to identify a₀'s position relative to the AP A' = A.erase a₀:
  a₀ = a₁ - d  (a₀ is the predecessor of AP A')
  OR
  a₀ = a₁ + |A'| * d  (a₀ is the successor of AP A')
-/
lemma ap_sdiff_endpoint (AP₁ AP₂ : Finset (ZMod p)) (s₁ s₂ d : ZMod p)
    (hAP₁ : IsArithmeticProgression AP₁ s₁ d)
    (hAP₂ : IsArithmeticProgression AP₂ s₂ d)
    (hd : d ≠ 0)
    (h₁ : 0 < AP₁.card)
    (h₁₂ : AP₁.card ≤ AP₂.card)
    (hlt : AP₁.card + AP₂.card ≤ p)
    (h_sdiff : (AP₁ \ AP₂).card = 1) :
    s₁ = s₂ - d ∨ s₁ = s₂ + ((AP₂.card - AP₁.card + 1 : ℕ) : ZMod p) * d := by
  sorry

/-
**Case 1 Existence**: In the inductive step of Vosper's theorem (|A| ≥ 3),
there always exists a "non-redundant" element a₀ ∈ A such that removing it
decreases the sumset cardinality.

The proof strategy:
1. Assume for contradiction that all a ∈ A are redundant (removing any a doesn't change |A+B|).
2. Show that all b ∈ B must also be redundant (using non_redundant_b_gives_a contrapositively).
3. Derive a contradiction:
   - For |B| = 2: use all_redundant_contradiction_B2.
   - For |B| = 3 with |A| = 3: counting argument gives 3*3 = 9 < 2*(3+3-1) = 10, contradiction.
   - General case: Cauchy-Davenport structure of ZMod p (prime order, no nontrivial subgroups)
     forces at least one element to be non-redundant.
-/
lemma case1_exists (A B : Finset (ZMod p))
    (hA3 : 2 < A.card) (hB : 2 ≤ B.card)
    (h : (A + B).card = A.card + B.card - 1)
    (hlt : A.card + B.card - 1 < p) :
    ∃ a₀ ∈ A, ((A.erase a₀) + B).card = A.card + B.card - 2 := by
  by_contra hall
  push_neg at hall
  -- All a ∈ A are redundant
  have hredA : ∀ a ∈ A, ((A.erase a) + B).card = A.card + B.card - 1 := by
    intro a haA
    have hlo := erase_add_card_ge A B a haA (by omega) (by omega) (by omega)
    have hhi := erase_add_card_le A B a
    rw [h] at hhi
    exact Nat.le_antisymm (by omega) (by exact (hall a haA).symm ▸ by omega)
  -- All b ∈ B are also redundant (by non_redundant_b_gives_a contrapositive)
  have hredB : ∀ b ∈ B, (A + (B.erase b)).card = A.card + B.card - 1 := by
    intro b hbB
    have hlo : A.card + B.card - 2 ≤ (A + (B.erase b)).card := by
      have hCD : (p ⊓ (A.card + (B.erase b).card - 1)) ≤ (A + B.erase b).card :=
        ZMod.cauchy_davenport hp.1
          (Finset.card_pos.mp (by omega))
          (Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hbB]; omega))
      rw [Finset.card_erase_of_mem hbB] at hCD
      simp only [Nat.inf_eq_min] at hCD
      omega
    have hhi : (A + (B.erase b)).card ≤ A.card + B.card - 1 := by
      have := Finset.card_le_card (Finset.add_subset_add_left (Finset.erase_subset b B))
      omega
    by_contra hne
    have hcard : (A + B.erase b).card = A.card + B.card - 2 := by omega
    obtain ⟨a₀, ha₀A, hcase1⟩ :=
      non_redundant_b_gives_a A B b hbB (by omega) hB h (by omega) hcard
    exact absurd hcase1 (by have := hredA a₀ ha₀A; omega)
  -- Both A and B are fully redundant. Derive contradiction via counting.
  -- Key: each x ∈ A+B has ≥ 2 distinct A-components, giving |A|·|B| ≥ 2·|A+B|.
  -- This requires: (|A|-2)·(|B|-2) ≥ 2, which fails for small |A|,|B|.
  -- Use all_redundant_contradiction_B2 for |B|=2, and counting for |B|=3 with |A|=3.
  sorry

end Erdos476OQ05Aristotle
