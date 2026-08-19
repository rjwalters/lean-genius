import Proofs.Erdos85SizeTwoMuNegThreeRefinedSectorRouting
import Proofs.Erdos85SizeTwoAlignedShoreSwitch
import Proofs.Erdos85EightEightCoordinateCover
import Proofs.Erdos85ComponentEigenvectorExtension
import Proofs.Erdos85ComponentSignFlipEigenvector

/-! # Graph-facing aligned shore switch for μ=-3 -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The refined aligned μ=-3 witness carries a genuine switched eigenvector.
The switch coefficient is the arithmetic table target, and `(1,2)` is its
unique fixed cell. -/
theorem orderSixtyFour_sizeTwo_muNegThree_refined_shoreSwitch
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
        s y = (-3 : ℤ) * s z)
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
    let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (u j)
    let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (v j)
    ∃ k r : ℕ, MuNegThreeRefinedSectorCells N₁ N₂ k r ∧
      let B := (Finset.univ : Finset c.supp).filter
        (fun x ↦ H.connectedComponentMk x = b)
      let t : c.supp → ℤ := fun x ↦ if x ∈ B then -s x.1 else s x.1
      (K.adjMatrix ℤ).mulVec t = sizeTwoMuSwitchTarget (-3) k r • t ∧
        (H.adjMatrix ℤ).mulVec t = (-2 : ℤ) • t ∧ t ≠ 0 ∧
        let T := connectedComponentExtendZero (secondOrderDefectGraph G) c
          (fun x ↦ (t x : ℚ))
        ((secondOrderDefectGraph G).adjMatrix ℚ).mulVec T =
            (sizeTwoMuSwitchTarget (-3) k r : ℚ) • T ∧ T ≠ 0 := by
  classical
  dsimp only
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  let B := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ b.supp
  let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (v i) (v j)
  obtain ⟨k, r, hcell, _ha8, _hb8, haa, habq, hbaq, hbb,
      hAA, hBB, hAB, hBA⟩ :=
    orderSixtyFour_sizeTwo_muNegThree_eightEight_refined_alignedLedger
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
        u v huinj hvinj hurange hvrange hu hv
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
  have hcover : ∀ x : c.supp, x ∈ a.supp ∨ x ∈ b.supp :=
    eightEight_shores_cover G c (by simpa using hc) a b hab
      u v huinj hvinj hurange hvrange
  have hsign : ∀ x : c.supp, s x.1 = -1 ∨ s x.1 = 1 := by
    intro x
    exact hs_in x.1 x.2
  have same_eq (p : (G.induce c.supp).ConnectedComponent)
      (P : Finset c.supp) (hP : P = Finset.univ.filter fun y ↦ y ∈ p.supp)
      (x : c.supp) :
      (P.filter fun y ↦ K.Adj x y ∧ s y.1 = s x.1) =
        (componentNeighborFinset K H p x).filter
          (fun y ↦ s y.1 = s x.1) := by
    subst P
    ext y
    simp [componentNeighborFinset, H, and_left_comm, and_assoc]
  have hAA' : ∀ x, x ∈ a.supp →
      ((componentNeighborFinset K H a x).filter
        (fun y ↦ s y.1 = s x.1)).card = k := by
    intro x hx
    rw [← same_eq a A rfl x]
    apply hAA x
    simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using hx
  have hAB' : ∀ x, x ∈ a.supp →
      ((componentNeighborFinset K H b x).filter
        (fun y ↦ s y.1 = s x.1)).card = 2 - k := by
    intro x hx
    rw [← same_eq b B rfl x]
    apply hAB x
    simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using hx
  have hBB' : ∀ x, x ∈ b.supp →
      ((componentNeighborFinset K H b x).filter
        (fun y ↦ s y.1 = s x.1)).card = k := by
    intro x hx
    rw [← same_eq b B rfl x]
    apply hBB x
    simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using hx
  have hBA' : ∀ x, x ∈ b.supp →
      ((componentNeighborFinset K H a x).filter
        (fun y ↦ s y.1 = s x.1)).card = 2 - k := by
    intro x hx
    rw [← same_eq a A rfl x]
    apply hBA x
    simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using hx
  refine ⟨k, r, hcell, ?_⟩
  have hswitch := twoComponent_quotient_signSwitch_adjMatrix_eigen_sub_of_card
    K H a b hab hdegree hcomm hcover (fun x ↦ s x.1)
      (7 - r) k r (2 - k) hsign haa habq hbaq hbb
      hAA' hAB' hBB' hBA'
  let t : c.supp → ℤ := fun x ↦
    if H.connectedComponentMk x = b then -s x.1 else s x.1
  have hcoeff :
      (2 * (k : ℤ) - (7 - r : ℕ)) - (2 * (2 - k : ℕ) - (r : ℤ)) =
        sizeTwoMuSwitchTarget (-3) k r := by
    rcases hcell with hzero | hmixed | hone
    · dsimp [MuNegThreeBothTriangleCell] at hzero
      rcases hzero.2.2 with h | h | h | h <;>
        rcases h with ⟨rfl, rfl⟩ <;> norm_num [sizeTwoMuSwitchTarget]
    · dsimp [MuNegThreeMixedCell] at hmixed
      rcases hmixed.2 with h | h <;>
        rcases h with ⟨rfl, rfl⟩ <;> norm_num [sizeTwoMuSwitchTarget]
    · rcases hone.2.2 with h | h | h | h | h <;>
        rcases h with ⟨rfl, rfl⟩ <;> norm_num [sizeTwoMuSwitchTarget]
  have heig : (K.adjMatrix ℤ).mulVec t =
      sizeTwoMuSwitchTarget (-3) k r • t := by
    simpa [t, hcoeff] using hswitch
  have ht : t ≠ 0 := by
    intro ht
    have hval := congrFun ht (u 0)
    have hsign0 := hs_in (u 0).1 (u 0).2
    by_cases hmem : H.connectedComponentMk (u 0) = b
    · simp [t, hmem] at hval
      omega
    · simp [t, hmem] at hval
      omega
  have hsH : (H.adjMatrix ℤ).mulVec (fun x : c.supp ↦ s x.1) =
      (-2 : ℤ) • (fun x : c.supp ↦ s x.1) := by
    funext x
    rw [induce_adjMatrix_mulVec_restrict_apply]
    have hx := hH x.1 x.2
    simpa [ConnectedComponent.mem_supp_iff, smul_eq_mul] using hx
  have htH := connectedComponent_signFlip_adjMatrix_eigenvector
    H b (fun x : c.supp ↦ s x.1) (-2) hsH
  have heigH : (H.adjMatrix ℤ).mulVec t = (-2 : ℤ) • t := by
    simpa [t] using htH
  refine ⟨by simpa [t, B] using heig, by simpa [t, B] using heigH,
    by simpa [t, B] using ht, ?_⟩
  have hglobal := adjMatrix_rat_nonzero_eigenvector_componentExtendZero_of_int
    (secondOrderDefectGraph G) c t
      (sizeTwoMuSwitchTarget (-3) k r) heig ht
  simpa [t, B] using hglobal

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_refined_shoreSwitch
