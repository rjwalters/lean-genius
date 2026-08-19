import Proofs.Erdos85SizeTwoAlignedShoreSwitch
import Proofs.Erdos85SizeTwoMuNegOneAlignedLedger
import Proofs.Erdos85SizeTwoMuNegOneRefinedSectorRouting
import Proofs.Erdos85ComponentSignFlipEigenvector
import Proofs.Erdos85SizeTwoSwitchedJointExclusions

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

/-- The refined aligned μ=-1 witness carries its genuine shore-flipped
defect eigenvector, with eigenvalue equal to the arithmetic switch target. -/
theorem orderSixtyFour_sizeTwo_muNegOne_refined_shoreSwitch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2) (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-1 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    let H := G.induce c.supp
    let K := (secondOrderDefectGraph G).induce c.supp
    let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ := fun i j ↦ K.adjMatrix ℤ (u i) (u j)
    let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ := fun i j ↦ K.adjMatrix ℤ (v i) (v j)
    ∃ k r : ℕ, MuNegOneRefinedSectorCells N₁ N₂ k r ∧
      let B := (Finset.univ : Finset c.supp).filter
        (fun x ↦ H.connectedComponentMk x = b)
      let t : c.supp → ℤ := fun x ↦ if x ∈ B then -s x.1 else s x.1
      (K.adjMatrix ℤ).mulVec t = sizeTwoMuSwitchTarget (-1) k r • t ∧
        (H.adjMatrix ℤ).mulVec t = (-2 : ℤ) • t ∧ t ≠ 0 ∧
          (∀ x, t x = -1 ∨ t x = 1) ∧
            sizeTwoMuSwitchTarget (-1) k r ≠ 1 := by
  classical
  dsimp only
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ := fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ := fun i j ↦ K.adjMatrix ℤ (v i) (v j)
  obtain ⟨k, r, hcell, ha8, hb8, haa, habq, hbaq, hbb,
      hAA, hBB, hAB, hBA⟩ :=
    orderSixtyFour_sizeTwo_muNegOne_eightEight_refined_alignedLedger
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
        u v huinj hvinj hurange hvrange hu hv
  have hsign : ∀ x : c.supp, s x.1 = -1 ∨ s x.1 = 1 :=
    fun x ↦ hs_in x.1 x.2
  refine ⟨k, r, hcell, ?_⟩
  have hswitch := orderSixtyFour_sizeTwo_alignedLedger_signSwitch
    G hfree hreg hcard c hc a b hab (fun x ↦ s x.1) hsign
      k r (3-k) ha8 hb8 haa habq hbaq hbb hAA hBB hAB hBA
  have hcoeff :
      (2 * (k : ℤ) - (7-r : ℕ)) - (2 * (3-k : ℕ) - (r : ℤ)) =
        sizeTwoMuSwitchTarget (-1) k r := by
    rcases hcell with hzero | hmixed | hone
    · rcases hzero.2 with h | h | h | h | h <;>
        rcases h with ⟨rfl, rfl⟩ <;> norm_num [sizeTwoMuSwitchTarget]
    · rcases hmixed.2 with h | h <;>
        rcases h with ⟨rfl, rfl⟩ <;> norm_num [sizeTwoMuSwitchTarget]
    · rcases hone.2 with h | h | h | h | h | h <;>
        rcases h with ⟨rfl, rfl⟩ <;> norm_num [sizeTwoMuSwitchTarget]
  have hsH : (H.adjMatrix ℤ).mulVec (fun x : c.supp ↦ s x.1) =
      (-2 : ℤ) • (fun x : c.supp ↦ s x.1) := by
    funext x
    rw [induce_adjMatrix_mulVec_restrict_apply]
    have hx := hH x.1 x.2
    simpa [ConnectedComponent.mem_supp_iff, smul_eq_mul] using hx
  have htH := connectedComponent_signFlip_adjMatrix_eigenvector
    H b (fun x : c.supp ↦ s x.1) (-2) hsH
  have htK : (K.adjMatrix ℤ).mulVec
      (fun x ↦ if x ∈ (Finset.univ : Finset c.supp).filter
        (fun y ↦ H.connectedComponentMk y = b) then -s x.1 else s x.1) =
      sizeTwoMuSwitchTarget (-1) k r •
        (fun x ↦ if x ∈ (Finset.univ : Finset c.supp).filter
          (fun y ↦ H.connectedComponentMk y = b) then -s x.1 else s x.1) := by
    simpa only [hcoeff] using hswitch
  have htH' : (H.adjMatrix ℤ).mulVec
      (fun x ↦ if x ∈ (Finset.univ : Finset c.supp).filter
        (fun y ↦ H.connectedComponentMk y = b) then -s x.1 else s x.1) =
      (-2 : ℤ) • (fun x ↦ if x ∈ (Finset.univ : Finset c.supp).filter
        (fun y ↦ H.connectedComponentMk y = b) then -s x.1 else s x.1) := by
    simpa [Finset.mem_filter] using htH
  have htne : (fun x ↦ if x ∈ (Finset.univ : Finset c.supp).filter
      (fun y ↦ H.connectedComponentMk y = b) then -s x.1 else s x.1) ≠ 0 := by
    intro ht
    have hval := congrFun ht (u 0)
    have hsign0 := hs_in (u 0).1 (u 0).2
    by_cases hmem : (u 0) ∈ (Finset.univ : Finset c.supp).filter
        (fun x ↦ H.connectedComponentMk x = b)
    · simp [hmem] at hval
      omega
    · simp [hmem] at hval
      omega
  have htsign : ∀ x, (if x ∈ (Finset.univ : Finset c.supp).filter
      (fun y ↦ H.connectedComponentMk y = b) then -s x.1 else s x.1) = -1 ∨
      (if x ∈ (Finset.univ : Finset c.supp).filter
        (fun y ↦ H.connectedComponentMk y = b) then -s x.1 else s x.1) = 1 := by
    intro x
    have hx := hs_in x.1 x.2
    by_cases hmem : x ∈ (Finset.univ : Finset c.supp).filter
        (fun y ↦ H.connectedComponentMk y = b)
    · simp only [hmem, if_true]
      omega
    · simp only [hmem, if_false]
      exact hx
  have htarget := orderSixtyFour_sizeTwoPart_inducedSignedJoint_switchTarget_ne_one
    G hfree hreg hcard c hc _ htsign (sizeTwoMuSwitchTarget (-1) k r)
      (by simpa [H] using htH') (by simpa [K] using htK)
  exact ⟨htK, htH', htne, htsign, htarget⟩

end


end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_alignedLedger_signSwitch
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_refined_shoreSwitch
