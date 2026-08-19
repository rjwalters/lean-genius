import Proofs.Erdos85SixTenBinaryCycleIntertwiner
import Proofs.Erdos85SizeTwoEigenlineSixTenCycleQuotient
import Proofs.Erdos85DefectCycleBlock

/-!
# Graph-facing checkerboard classification of the q=8 six-plus-ten cross block

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The exact cross quotient gives row sum five.  In cyclic coordinates,
commutation supplies the `6 × 10` cycle recurrence.  The pure binary
intertwiner classifier then forces every unit step in either coordinate to
complement the cross-defect adjacency bit.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Row sum five discharges the nonconstancy hypothesis of the pure binary
`6 × 10` checkerboard classifier. -/
theorem binary_sixTenCycleIntertwiner_checkerboard_of_rowSum_five
    (B : Matrix (ZMod 6) (ZMod 10) ℤ)
    (hinter : ∀ x y,
      B (x - 1) y + B (x + 1) y =
        B x (y + 1) + B x (y - 1))
    (hbinary : ∀ x y, B x y = 0 ∨ B x y = 1)
    (hrows : ∀ x, ∑ y, B x y = 5) :
    (∀ x y, B x (y + 1) = 1 - B x y) ∧
      (∀ x y, B (x + 1) y = 1 - B x y) := by
  apply binary_sixTenCycleIntertwiner_checkerboard B hinter hbinary
  intro x
  by_contra hconstant
  push Not at hconstant
  have hrow := hrows x
  rcases hbinary x 0 with hzero | hone
  · have hz : ∀ y, B x y = 0 := by
      intro y
      exact (hconstant y 0).trans hzero
    simp_rw [hz] at hrow
    norm_num at hrow
  · have ho : ∀ y, B x y = 1 := by
      intro y
      exact (hconstant y 0).trans hone
    simp_rw [ho] at hrow
    norm_num at hrow

/-- In any cyclic coordinates on the internal six- and ten-cycles, the
cross-defect block is one of the two complementary checkerboards. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_crossDefect_checkerboard_of_coordinates
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10)
    (u : ZMod 6 → c.supp) (v : ZMod 10 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    (∀ i j,
      ((secondOrderDefectGraph G).induce c.supp).Adj (u i) (v (j + 1)) ↔
        ¬ ((secondOrderDefectGraph G).induce c.supp).Adj (u i) (v j)) ∧
      (∀ i j,
      ((secondOrderDefectGraph G).induce c.supp).Adj (u (i + 1)) (v j) ↔
        ¬ ((secondOrderDefectGraph G).induce c.supp).Adj (u i) (v j)) := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let B : Matrix (ZMod 6) (ZMod 10) ℤ :=
    fun i j => K.adjMatrix ℤ (u i) (v j)
  obtain ⟨hHdegree, _hKdegree, hcommHK⟩ :=
    binarySquare_regular_sizeTwoPart_commuting_regular_blocks
      G hfree (by omega) hreg hcard c hc
  have hcommKH : K.adjMatrix ℤ * H.adjMatrix ℤ =
      H.adjMatrix ℤ * K.adjMatrix ℤ := by
    simpa [K, H] using hcommHK.symm
  have hupair : ∀ z : ZMod 6, u (z - 1) ≠ u (z + 1) := by
    intro z heq
    have hz : z - 1 = z + 1 := huinj heq
    have htwo : (2 : ZMod 6) = 0 := by
      calc
        (2 : ZMod 6) = (z + 1) - (z - 1) := by ring
        _ = 0 := by rw [← hz]; simp
    exact (by decide : (2 : ZMod 6) ≠ 0) htwo
  have hvpair : ∀ z : ZMod 10, v (z - 1) ≠ v (z + 1) := by
    intro z heq
    have hz : z - 1 = z + 1 := hvinj heq
    have htwo : (2 : ZMod 10) = 0 := by
      calc
        (2 : ZMod 10) = (z + 1) - (z - 1) := by ring
        _ = 0 := by rw [← hz]; simp
    exact (by decide : (2 : ZMod 10) ≠ 0) htwo
  have hinter : ∀ i j,
      B (i - 1) j + B (i + 1) j =
        B i (j + 1) + B i (j - 1) := by
    exact entry_cycleIntertwine_of_adjMatrix_comm K H u v
      (1 : ZMod 6) (1 : ZMod 10) hcommKH hu hv hupair hvpair
  have hbinary : ∀ i j, B i j = 0 ∨ B i j = 1 := by
    intro i j
    simp only [B, SimpleGraph.adjMatrix_apply]
    split <;> simp
  have hrowCard (i : ZMod 6) :
      ((Finset.univ : Finset (ZMod 10)).filter fun j => K.Adj (u i) (v j)).card = 5 := by
    let S := (Finset.univ : Finset (ZMod 10)).filter fun j => K.Adj (u i) (v j)
    have himage : S.image v = componentNeighborFinset K H b (u i) := by
      ext z
      simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, componentNeighborFinset]
      constructor
      · rintro ⟨j, hij, rfl⟩
        refine ⟨(K.mem_neighborFinset (u i) (v j)).mpr hij, ?_⟩
        exact (ConnectedComponent.mem_supp_iff b (v j)).mp
          (by rw [← hvrange]; exact ⟨j, rfl⟩)
      · rintro ⟨hzK, hzb⟩
        have hzB : z ∈ b.supp := (ConnectedComponent.mem_supp_iff b z).mpr hzb
        rw [← hvrange] at hzB
        obtain ⟨j, rfl⟩ := hzB
        exact ⟨j, (K.mem_neighborFinset (u i) (v j)).mp hzK, rfl⟩
    have hcardImage : S.card = (componentNeighborFinset K H b (u i)).card := by
      calc
        S.card = (S.image v).card :=
          (Finset.card_image_of_injective _ hvinj).symm
        _ = _ := congrArg Finset.card himage
    rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree
      (by
        have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
          (K := ℝ) G hfree hreg
        exact (induce_component_adjMatrix_comm_of_comm
          G (secondOrderDefectGraph G) hglobal c).symm)
      a b (by rw [← hurange]; exact ⟨i, rfl⟩)] at hcardImage
    rw [(binarySquare_regular_sizeTwoPart_eight_sixTen_cycleQuotient
      G hfree hreg hcard c hc s hs_in hs_out hA_in a b ha hb).2.1] at hcardImage
    simpa [S] using hcardImage
  have hrows : ∀ i, ∑ j, B i j = 5 := by
    intro i
    have hc := hrowCard i
    change (∑ j, if K.Adj (u i) (v j) then (1 : ℤ) else 0) = 5
    rw [Finset.sum_boole]
    exact_mod_cast hc
  obtain ⟨htarget, hsource⟩ :=
    binary_sixTenCycleIntertwiner_checkerboard_of_rowSum_five
      B hinter hbinary hrows
  constructor
  · intro i j
    have hflip := htarget i j
    simp only [B, SimpleGraph.adjMatrix_apply] at hflip
    constructor
    · intro hadj hbase
      rw [if_pos hadj, if_pos hbase] at hflip
      omega
    · intro hnot
      by_contra hnext
      rw [if_neg hnext, if_neg hnot] at hflip
      omega
  · intro i j
    have hflip := hsource i j
    simp only [B, SimpleGraph.adjMatrix_apply] at hflip
    constructor
    · intro hadj hbase
      rw [if_pos hadj, if_pos hbase] at hflip
      omega
    · intro hnot
      by_contra hnext
      rw [if_neg hnext, if_neg hnot] at hflip
      omega

end

end Erdos85

#print axioms Erdos85.binary_sixTenCycleIntertwiner_checkerboard_of_rowSum_five
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_crossDefect_checkerboard_of_coordinates
