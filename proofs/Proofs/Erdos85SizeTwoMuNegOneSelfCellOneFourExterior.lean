import Proofs.Erdos85SizeTwoEigenlineEightEightHighParameterCrossBlock
import Proofs.Erdos85SizeTwoMuNegOneSelfCellOneFourShape

/-! # Exterior structure of the mu=-1, (k,r)=(1,4) self cell -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

theorem binarySquare_regular_sizeTwoPart_eight_eightEight_parameterFour_crossExterior_degrees
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8) (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 8) (hb : b.supp.ncard = 8) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hab4 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 4) :
    (∀ i, ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      (exteriorPairGraph G c.supp).Adj (u i) (v j)).card = 4) ∧
    (∀ j, ((Finset.univ : Finset (ZMod 8)).filter fun i ↦
      (exteriorPairGraph G c.supp).Adj (u i) (v j)).card = 4) := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let R := exteriorPairGraph G c.supp
  have hHdegree : ∀ z : c.supp, H.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2) hc z
  have hcomm : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm
      G (secondOrderDefectGraph G) hglobal c).symm
  have hba4 : componentQuotientMatrix K H b a = 4 := by
    have hbal := componentQuotientMatrix_balance K H 2 hHdegree hcomm a b
    change a.supp.ncard * componentQuotientMatrix K H a b =
      b.supp.ncard * componentQuotientMatrix K H b a at hbal
    rw [ha, hb] at hbal
    have hab4' : componentQuotientMatrix K H a b = 4 := by
      simpa [K, H] using hab4
    rw [hab4'] at hbal
    omega
  have hcompUV := sizeTwo_distinctCycle_cross_exteriorPair_iff_not_defect
    G hfree c a b hab u v hurange hvrange
  have hcompVU : ∀ j i, R.Adj (v j) (u i) ↔ ¬ K.Adj (v j) (u i) := by
    intro j i
    rw [R.adj_comm, K.adj_comm]
    exact hcompUV i j
  have rowCard
      (w z : ZMod 8 → c.supp)
      (hzinj : Function.Injective z)
      (d e : H.ConnectedComponent)
      (hwmem : ∀ x, w x ∈ d.supp)
      (hzrange : Set.range z = e.supp)
      (hde : componentQuotientMatrix K H d e = 4)
      (hcomp : ∀ x y, R.Adj (w x) (z y) ↔ ¬ K.Adj (w x) (z y)) :
      ∀ x, ((Finset.univ : Finset (ZMod 8)).filter fun y ↦
        R.Adj (w x) (z y)).card = 4 := by
    intro x
    let T := (Finset.univ : Finset (ZMod 8)).filter fun y ↦
      K.Adj (w x) (z y)
    let B := componentNeighborFinset K H e (w x)
    have himage : T.image z = B := by
      ext q
      simp only [T, B, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and, componentNeighborFinset]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨(K.mem_neighborFinset _ _).mpr hy,
          (ConnectedComponent.mem_supp_iff e (z y)).mp (by
            rw [← hzrange]; exact ⟨y, rfl⟩)⟩
      · rintro ⟨hqK, hqe⟩
        have hqSupp : q ∈ e.supp :=
          (ConnectedComponent.mem_supp_iff e q).mpr hqe
        rw [← hzrange] at hqSupp
        obtain ⟨y, rfl⟩ := hqSupp
        exact ⟨y, (K.mem_neighborFinset _ _).mp hqK, rfl⟩
    have hTcard : T.card = 4 := by
      rw [← Finset.card_image_of_injective T hzinj, himage]
      rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcomm d e
        (hwmem x)]
      exact hde
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (ZMod 8)))
      (p := fun y ↦ K.Adj (w x) (z y))
    have hRfilter :
        ((Finset.univ : Finset (ZMod 8)).filter fun y ↦
          R.Adj (w x) (z y)) =
        (Finset.univ.filter fun y ↦ ¬ K.Adj (w x) (z y)) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hcomp x y
    rw [hRfilter]
    change T.card + _ = 8 at hpartition
    rw [hTcard] at hpartition
    omega
  constructor
  · apply rowCard u v hvinj a b
    · intro i
      rw [← hurange]
      exact ⟨i, rfl⟩
    · exact hvrange
    · simpa [K, H] using hab4
    · exact hcompUV
  · intro j
    have h := rowCard v u huinj b a (fun k ↦ by
      rw [← hvrange]; exact ⟨k, rfl⟩) hurange hba4 hcompVU j
    simpa only [R.adj_comm] using h

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_parameterFour_crossExterior_degrees
