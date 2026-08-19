import Proofs.Erdos85SizeTwoAlignedShoreSwitch
import Proofs.Erdos85SizeTwoMuNegOneAlignedLedger

/-! # Graph-facing aligned shore switch for the μ=-1 lane -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The quotient and signed-row fields retained by the aligned ledger produce
the switched defect eigenvector without any witness realignment. -/
theorem orderSixtyFour_sizeTwo_alignedLedger_signSwitch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (s : c.supp → ℤ) (hsign : ∀ x, s x = -1 ∨ s x = 1)
    (k r crossSame : ℕ)
    (ha8 : a.supp.ncard = 8) (hb8 : b.supp.ncard = 8)
    (haa : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 7 - r)
    (habq : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = r)
    (hbaq : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b a = r)
    (hbb : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b b = 7 - r)
    (hAA : ∀ x ∈ (Finset.univ : Finset c.supp).filter (fun x ↦ x ∈ a.supp),
      (((Finset.univ : Finset c.supp).filter (fun x ↦ x ∈ a.supp)).filter
        fun y ↦ ((secondOrderDefectGraph G).induce c.supp).Adj x y ∧
          s y = s x).card = k)
    (hBB : ∀ x ∈ (Finset.univ : Finset c.supp).filter (fun x ↦ x ∈ b.supp),
      (((Finset.univ : Finset c.supp).filter (fun x ↦ x ∈ b.supp)).filter
        fun y ↦ ((secondOrderDefectGraph G).induce c.supp).Adj x y ∧
          s y = s x).card = k)
    (hAB : ∀ x ∈ (Finset.univ : Finset c.supp).filter (fun x ↦ x ∈ a.supp),
      (((Finset.univ : Finset c.supp).filter (fun x ↦ x ∈ b.supp)).filter
        fun y ↦ ((secondOrderDefectGraph G).induce c.supp).Adj x y ∧
          s y = s x).card = crossSame)
    (hBA : ∀ x ∈ (Finset.univ : Finset c.supp).filter (fun x ↦ x ∈ b.supp),
      (((Finset.univ : Finset c.supp).filter (fun x ↦ x ∈ a.supp)).filter
        fun y ↦ ((secondOrderDefectGraph G).induce c.supp).Adj x y ∧
          s y = s x).card = crossSame) :
    let H := G.induce c.supp
    let K := (secondOrderDefectGraph G).induce c.supp
    let B := (Finset.univ : Finset c.supp).filter
      (fun x ↦ H.connectedComponentMk x = b)
    let t : c.supp → ℤ := fun x ↦ if x ∈ B then -s x else s x
    (K.adjMatrix ℤ).mulVec t =
      ((2 * (k : ℤ) - (7 - r : ℕ)) -
        (2 * (crossSame : ℤ) - r)) • t := by
  classical
  dsimp only
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  let B := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ b.supp
  have hAcard : A.card = 8 := by
    have heq : A = a.supp.toFinite.toFinset := by ext x; simp [A]
    rw [heq, ← Set.ncard_eq_toFinset_card, ha8]
  have hBcard : B.card = 8 := by
    have heq : B = b.supp.toFinite.toFinset := by ext x; simp [B]
    rw [heq, ← Set.ncard_eq_toFinset_card, hb8]
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxa hxb
    exact hab <| (ConnectedComponent.mem_supp_iff a x).mp
      (Finset.mem_filter.mp hxa).2 |>.symm.trans
        ((ConnectedComponent.mem_supp_iff b x).mp (Finset.mem_filter.mp hxb).2)
  have hcoverFin : A ∪ B = (Finset.univ : Finset c.supp) := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_union_of_disjoint hdisj, hAcard, hBcard,
      Finset.card_univ]
    have hsuppcard : Fintype.card c.supp = 16 := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hc]
    omega
  have hpartition : ∀ x : c.supp, x ∈ a.supp ∨ x ∈ b.supp := by
    intro x
    have hx : x ∈ A ∪ B := by rw [hcoverFin]; exact Finset.mem_univ x
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Or.inl (Finset.mem_filter.mp hx).2
    · exact Or.inr (Finset.mem_filter.mp hx).2
  have hdegree : ∀ x : c.supp, H.degree x = 2 := by
    intro x
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2) hc x
  have hcomm : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm G
      (secondOrderDefectGraph G) hglobal c).symm
  have hsame (d : H.ConnectedComponent)
      (F : Finset c.supp) (hF : F = (Finset.univ : Finset c.supp).filter
        fun x ↦ x ∈ d.supp) (x : c.supp) :
      ((componentNeighborFinset K H d x).filter fun y ↦ s y = s x).card =
        (F.filter fun y ↦ K.Adj x y ∧ s y = s x).card := by
    congr 1
    ext y
    simp [componentNeighborFinset, hF, SimpleGraph.mem_neighborFinset,
      and_left_comm, and_assoc]
  apply twoComponent_quotient_signSwitch_adjMatrix_eigen_sub_of_card
    K H a b hab hdegree hcomm hpartition s (7-r) k r crossSame hsign
    haa habq hbaq hbb
  · intro x hx
    rw [hsame a A rfl x]
    exact hAA x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)
  · intro x hx
    rw [hsame b B rfl x]
    exact hAB x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)
  · intro x hx
    rw [hsame b B rfl x]
    exact hBB x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)
  · intro x hx
    rw [hsame a A rfl x]
    exact hBA x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)

end


end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_alignedLedger_signSwitch
