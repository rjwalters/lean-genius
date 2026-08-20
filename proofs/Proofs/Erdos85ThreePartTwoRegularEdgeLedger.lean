import Proofs.Erdos85OddSquareOrderNineIncidenceQuotientSymmetry

/-! # Edge ledger for balanced three-part two-regular graphs

A two-regular graph partitioned into three independent parts of equal size
has the same number of edges between every pair of parts.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In a two-regular graph partitioned into three independent `n`-vertex
parts, every pair of parts carries exactly `n` edges.  Cross-edge counts are
written as directed incidence sums, equal to ordinary edge counts here. -/
theorem threePart_twoRegular_crossEdge_ledger
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (A B C : Finset V) (n : ℕ)
    (hcover : A ∪ B ∪ C = Finset.univ)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hAcard : A.card = n) (hBcard : B.card = n) (hCcard : C.card = n)
    (hdeg : ∀ x : V, D.degree x = 2)
    (hAind : ∀ x ∈ A, (D.neighborFinset x ∩ A).card = 0)
    (hBind : ∀ x ∈ B, (D.neighborFinset x ∩ B).card = 0)
    (hCind : ∀ x ∈ C, (D.neighborFinset x ∩ C).card = 0) :
    (∑ x ∈ A, (D.neighborFinset x ∩ B).card) = n ∧
      (∑ x ∈ B, (D.neighborFinset x ∩ C).card) = n ∧
      (∑ x ∈ C, (D.neighborFinset x ∩ A).card) = n := by
  classical
  have hneighborPartition (x : V) : D.neighborFinset x =
      ((D.neighborFinset x ∩ A) ∪ (D.neighborFinset x ∩ B)) ∪
        (D.neighborFinset x ∩ C) := by
    ext y
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro hy
      have hyU : y ∈ A ∪ B ∪ C := by rw [hcover]; simp
      rcases Finset.mem_union.mp hyU with hyAB | hyC
      · rcases Finset.mem_union.mp hyAB with hyA | hyB
        · exact Or.inl (Or.inl ⟨hy, hyA⟩)
        · exact Or.inl (Or.inr ⟨hy, hyB⟩)
      · exact Or.inr ⟨hy, hyC⟩
    · rintro (⟨⟨hy, _⟩ | ⟨hy, _⟩⟩ | ⟨hy, _⟩) <;> exact hy
  have hrowA :
      (∑ x ∈ A, (D.neighborFinset x ∩ B).card) +
        (∑ x ∈ A, (D.neighborFinset x ∩ C).card) = 2 * n := by
    have hpoint : ∀ x ∈ A,
        (D.neighborFinset x ∩ B).card +
          (D.neighborFinset x ∩ C).card = 2 := by
      intro x hx
      have hdisjAB : Disjoint (D.neighborFinset x ∩ A)
          (D.neighborFinset x ∩ B) :=
        hAB.mono Finset.inter_subset_right Finset.inter_subset_right
      have hdisjABC : Disjoint
          ((D.neighborFinset x ∩ A) ∪ (D.neighborFinset x ∩ B))
          (D.neighborFinset x ∩ C) := by
        rw [Finset.disjoint_union_left]
        exact ⟨
          hAC.mono Finset.inter_subset_right Finset.inter_subset_right,
          hBC.mono Finset.inter_subset_right Finset.inter_subset_right⟩
      have hc := congrArg Finset.card (hneighborPartition x)
      rw [Finset.card_union_of_disjoint hdisjABC,
        Finset.card_union_of_disjoint hdisjAB,
        D.card_neighborFinset_eq_degree, hdeg x, hAind x hx] at hc
      omega
    calc
      (∑ x ∈ A, (D.neighborFinset x ∩ B).card) +
          (∑ x ∈ A, (D.neighborFinset x ∩ C).card) =
          ∑ x ∈ A, ((D.neighborFinset x ∩ B).card +
            (D.neighborFinset x ∩ C).card) := by rw [Finset.sum_add_distrib]
      _ = ∑ _x ∈ A, 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hpoint x hx
      _ = 2 * n := by simp [hAcard, Nat.mul_comm]
  have hrowB :
      (∑ x ∈ B, (D.neighborFinset x ∩ A).card) +
        (∑ x ∈ B, (D.neighborFinset x ∩ C).card) = 2 * n := by
    have hpoint : ∀ x ∈ B,
        (D.neighborFinset x ∩ A).card +
          (D.neighborFinset x ∩ C).card = 2 := by
      intro x hx
      have hc := congrArg Finset.card (hneighborPartition x)
      have hdisjAB' : Disjoint (D.neighborFinset x ∩ A)
          (D.neighborFinset x ∩ B) :=
        hAB.mono Finset.inter_subset_right Finset.inter_subset_right
      have hdisjABC : Disjoint
          ((D.neighborFinset x ∩ A) ∪ (D.neighborFinset x ∩ B))
          (D.neighborFinset x ∩ C) := by
        rw [Finset.disjoint_union_left]
        exact ⟨
          hAC.mono Finset.inter_subset_right Finset.inter_subset_right,
          hBC.mono Finset.inter_subset_right Finset.inter_subset_right⟩
      rw [Finset.card_union_of_disjoint hdisjABC,
        Finset.card_union_of_disjoint hdisjAB',
        D.card_neighborFinset_eq_degree, hdeg x, hBind x hx] at hc
      omega
    calc
      _ = ∑ x ∈ B, ((D.neighborFinset x ∩ A).card +
            (D.neighborFinset x ∩ C).card) := by rw [Finset.sum_add_distrib]
      _ = ∑ _x ∈ B, 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hpoint x hx
      _ = 2 * n := by simp [hBcard, Nat.mul_comm]
  have hrowC :
      (∑ x ∈ C, (D.neighborFinset x ∩ A).card) +
        (∑ x ∈ C, (D.neighborFinset x ∩ B).card) = 2 * n := by
    have hpoint : ∀ x ∈ C,
        (D.neighborFinset x ∩ A).card +
          (D.neighborFinset x ∩ B).card = 2 := by
      intro x hx
      have hc := congrArg Finset.card (hneighborPartition x)
      have hdisjAB' : Disjoint (D.neighborFinset x ∩ A)
          (D.neighborFinset x ∩ B) :=
        hAB.mono Finset.inter_subset_right Finset.inter_subset_right
      have hdisjABC : Disjoint
          ((D.neighborFinset x ∩ A) ∪ (D.neighborFinset x ∩ B))
          (D.neighborFinset x ∩ C) := by
        rw [Finset.disjoint_union_left]
        exact ⟨
          hAC.mono Finset.inter_subset_right Finset.inter_subset_right,
          hBC.mono Finset.inter_subset_right Finset.inter_subset_right⟩
      rw [Finset.card_union_of_disjoint hdisjABC,
        Finset.card_union_of_disjoint hdisjAB',
        D.card_neighborFinset_eq_degree, hdeg x, hCind x hx] at hc
      omega
    calc
      _ = ∑ x ∈ C, ((D.neighborFinset x ∩ A).card +
            (D.neighborFinset x ∩ B).card) := by rw [Finset.sum_add_distrib]
      _ = ∑ _x ∈ C, 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hpoint x hx
      _ = 2 * n := by simp [hCcard, Nat.mul_comm]
  have hsAB := sum_card_neighborFinset_inter_comm D A B
  have hsAC := sum_card_neighborFinset_inter_comm D A C
  have hsBC := sum_card_neighborFinset_inter_comm D B C
  omega

/-- If the common part size is odd, some vertex of the first part has one
neighbor in each of the other two parts.  This is the local ``rainbow
wedge'' forced by the odd cross-edge ledger. -/
theorem threePart_twoRegular_exists_cross_wedge_of_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (A B C : Finset V) (n : ℕ)
    (hcover : A ∪ B ∪ C = Finset.univ)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hAcard : A.card = n) (hBcard : B.card = n) (hCcard : C.card = n)
    (hdeg : ∀ x : V, D.degree x = 2)
    (hAind : ∀ x ∈ A, (D.neighborFinset x ∩ A).card = 0)
    (hBind : ∀ x ∈ B, (D.neighborFinset x ∩ B).card = 0)
    (hCind : ∀ x ∈ C, (D.neighborFinset x ∩ C).card = 0)
    (hn : Odd n) :
    ∃ x ∈ A, (D.neighborFinset x ∩ B).card = 1 ∧
      (D.neighborFinset x ∩ C).card = 1 := by
  classical
  have hledger := threePart_twoRegular_crossEdge_ledger D A B C n
    hcover hAB hAC hBC hAcard hBcard hCcard hdeg hAind hBind hCind
  have hsum : Odd (∑ x ∈ A, (D.neighborFinset x ∩ B).card) := by
    rw [hledger.1]
    exact hn
  have hoddCard : Odd ({x ∈ A |
      Odd ((D.neighborFinset x ∩ B).card)}).card :=
    (Finset.odd_sum_iff_odd_card_odd
      (fun x => (D.neighborFinset x ∩ B).card)).mp hsum
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hoddCard.pos
  have hx' := Finset.mem_filter.mp hx
  have hB_le : (D.neighborFinset x ∩ B).card ≤ 2 := by
    calc
      (D.neighborFinset x ∩ B).card ≤ (D.neighborFinset x).card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = D.degree x := D.card_neighborFinset_eq_degree x
      _ = 2 := hdeg x
  have hB_one : (D.neighborFinset x ∩ B).card = 1 := by
    obtain ⟨k, hk⟩ := hx'.2
    omega
  have hneighborPartition : D.neighborFinset x =
      ((D.neighborFinset x ∩ A) ∪ (D.neighborFinset x ∩ B)) ∪
        (D.neighborFinset x ∩ C) := by
    ext y
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro hy
      have hyU : y ∈ A ∪ B ∪ C := by rw [hcover]; simp
      rcases Finset.mem_union.mp hyU with hyAB | hyC
      · rcases Finset.mem_union.mp hyAB with hyA | hyB
        · exact Or.inl (Or.inl ⟨hy, hyA⟩)
        · exact Or.inl (Or.inr ⟨hy, hyB⟩)
      · exact Or.inr ⟨hy, hyC⟩
    · rintro (⟨⟨hy, _⟩ | ⟨hy, _⟩⟩ | ⟨hy, _⟩) <;> exact hy
  have hdisjAB : Disjoint (D.neighborFinset x ∩ A)
      (D.neighborFinset x ∩ B) :=
    hAB.mono Finset.inter_subset_right Finset.inter_subset_right
  have hdisjABC : Disjoint
      ((D.neighborFinset x ∩ A) ∪ (D.neighborFinset x ∩ B))
      (D.neighborFinset x ∩ C) := by
    rw [Finset.disjoint_union_left]
    exact ⟨
      hAC.mono Finset.inter_subset_right Finset.inter_subset_right,
      hBC.mono Finset.inter_subset_right Finset.inter_subset_right⟩
  have hc := congrArg Finset.card hneighborPartition
  rw [Finset.card_union_of_disjoint hdisjABC,
    Finset.card_union_of_disjoint hdisjAB,
    D.card_neighborFinset_eq_degree, hdeg x, hAind x hx'.1, hB_one] at hc
  exact ⟨x, hx'.1, hB_one, by omega⟩

end

end Erdos85

#print axioms Erdos85.threePart_twoRegular_crossEdge_ledger
#print axioms Erdos85.threePart_twoRegular_exists_cross_wedge_of_odd
