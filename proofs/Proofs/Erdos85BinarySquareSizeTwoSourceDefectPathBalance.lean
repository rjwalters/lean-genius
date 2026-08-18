import Proofs.Erdos85BinarySquareSizeTwoSourceLineGraph
import Proofs.Erdos85RestrictedOwnerCommutesInducedDefect
import Proofs.Erdos85AlternatingFourthMoment

/-! # Selector/defect path balance inside a source component -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **q-generic selector/defect coupling.**  Fix a size-two owner coordinate
and a source defect component.  At every ordered source pair `x,y`, the
number of source vertices whose selector meets the selector of `x` and then
takes a defect edge to `y` equals the reverse-order count.  This is the
pointwise, canonically labeled form of restricted owner/defect commutation. -/
theorem binarySquare_regular_sizeTwoPart_source_selector_defect_path_card_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (source owner : (secondOrderDefectGraph G).ConnectedComponent)
    (howner : owner.supp.ncard = q * 2) (x y : source.supp) :
    ((Finset.univ : Finset source.supp).filter fun z =>
        x ≠ z ∧
          (componentNeighborFinset G (secondOrderDefectGraph G) owner x.1 ∩
            componentNeighborFinset G (secondOrderDefectGraph G) owner z.1).Nonempty ∧
          (secondOrderDefectGraph G).Adj z.1 y.1).card =
      ((Finset.univ : Finset source.supp).filter fun z =>
        (secondOrderDefectGraph G).Adj x.1 z.1 ∧ z ≠ y ∧
          (componentNeighborFinset G (secondOrderDefectGraph G) owner z.1 ∩
            componentNeighborFinset G (secondOrderDefectGraph G) owner y.1).Nonempty).card := by
  let O := restrictedComponentOwnerGraph G source owner
  let D := (secondOrderDefectGraph G).induce source.supp
  have hcomm : O.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * O.adjMatrix ℤ :=
    binarySquare_regular_restrictedOwner_adjMatrix_comm_inducedDefect
      G hfree hq hreg hcard source owner howner
  have hentry := congrArg (fun M : Matrix source.supp source.supp ℤ => M x y) hcomm
  rw [adjMatrix_mul_subgraph_apply_eq_card_mixed,
    adjMatrix_mul_subgraph_apply_eq_card_mixed] at hentry
  have hcount :
      (O.neighborFinset x ∩ D.neighborFinset y).card =
        (D.neighborFinset x ∩ O.neighborFinset y).card := by
    exact_mod_cast hentry
  have hleft :
      (O.neighborFinset x ∩ D.neighborFinset y) =
        (Finset.univ : Finset source.supp).filter fun z =>
          x ≠ z ∧
            (componentNeighborFinset G (secondOrderDefectGraph G) owner x.1 ∩
              componentNeighborFinset G (secondOrderDefectGraph G) owner z.1).Nonempty ∧
            (secondOrderDefectGraph G).Adj z.1 y.1 := by
    ext z
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp [O, D, restrictedComponentOwnerGraph]
    simp only [SimpleGraph.induce_adj]
    dsimp [componentOwnerGraph]
    constructor
    · rintro ⟨⟨hxz, hinter⟩, hD⟩
      have hxz' : x ≠ z := fun h => hxz (congrArg Subtype.val h)
      exact ⟨hxz', hinter, hD.symm⟩
    · rintro ⟨hxz, hinter, hD⟩
      have hxz' : x.1 ≠ z.1 := by
        intro h
        exact hxz (Subtype.ext h)
      exact ⟨⟨hxz', hinter⟩, hD.symm⟩
  have hright :
      (D.neighborFinset x ∩ O.neighborFinset y) =
        (Finset.univ : Finset source.supp).filter fun z =>
          (secondOrderDefectGraph G).Adj x.1 z.1 ∧ z ≠ y ∧
            (componentNeighborFinset G (secondOrderDefectGraph G) owner z.1 ∩
              componentNeighborFinset G (secondOrderDefectGraph G) owner y.1).Nonempty := by
    ext z
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp [O, D, restrictedComponentOwnerGraph]
    simp only [SimpleGraph.induce_adj]
    dsimp [componentOwnerGraph]
    constructor
    · rintro ⟨hD, hyz, hinter⟩
      have hyz' : y ≠ z := fun h => hyz (congrArg Subtype.val h)
      exact ⟨hD, hyz'.symm, by simpa [Finset.inter_comm] using hinter⟩
    · rintro ⟨hD, hzy, hinter⟩
      have hyz : y.1 ≠ z.1 := by
        intro h
        exact hzy (Subtype.ext h.symm)
      exact ⟨hD, hyz, by simpa [Finset.inter_comm] using hinter⟩
  rw [← hleft, ← hright]
  exact hcount

end

end Erdos85
