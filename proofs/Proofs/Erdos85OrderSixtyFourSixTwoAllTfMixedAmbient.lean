import Proofs.Erdos85OrderSixtyFourMuThreeAllTfTriangleFortyEight
import Proofs.Erdos85CyclicUniqueSectorFactorThree
import Proofs.Erdos85BinarySquareCrossTriangleLiteralMixed

/-!
# The exact mixed-ambient count in the `[6,2]` stratum

With exactly two defect components, every multi-component triangle meets the
size-sixteen component.  If that component is all triangle-free, exterior
support makes its vertex unique.  Cyclic symmetry therefore turns the 96
first-root ordered pairs into 288 globally ordered triples.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 4096 in
/-- **The `[6,2]` exact 288 count.** -/
theorem orderSixtyFour_sixTwo_allTf_multiComponentAmbient_card_eq_288
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16)
    (hcomponents : ∀ d : (secondOrderDefectGraph G).ConnectedComponent,
      d = c ∨ d = e)
    (htf : ∀ x : c.supp, (triangleFreeEdgeGraph G).degree x.1 = 2) :
    (multiComponentAmbientCyclicTriangles G).card = 288 := by
  classical
  let D := secondOrderDefectGraph G
  let M := multiComponentAmbientCyclicTriangles G
  have hroot96 :=
    orderSixtyFour_allSixteen_tfComponent_sum_rootedCyclicPairs_eq_ninetySix
      G hfree hreg c hc htf
  have hinterior (x : c.supp) {y z : Fin 64}
      (hxy : G.Adj x.1 y) (hxz : G.Adj x.1 z) (hyz : G.Adj y z) :
      y ∉ c.supp ∧ z ∉ c.supp :=
    orderSixtyFour_allSixteen_tfComponent_rooted_triangle_endpoints_exterior
      G hfree hreg c hc htf x hxy hxz hyz
  have hrotate (p : Fin 64 × Fin 64 × Fin 64) :
      p ∈ M ↔ (p.2.2, p.1, p.2.1) ∈ M := by
    rcases p with ⟨x, z, y⟩
    simp only [M, multiComponentAmbientCyclicTriangles,
      cyclicColoredTriples, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hxy, hyz, hzx⟩, hcross⟩
      refine ⟨⟨hyz, hzx, hxy⟩, ?_⟩
      rintro ⟨hyxComp, hyzComp⟩
      apply hcross
      exact ⟨hyxComp.symm.trans hyzComp, hyxComp.symm⟩
    · rintro ⟨⟨hyz, hzx, hxy⟩, hcross⟩
      refine ⟨⟨hxy, hyz, hzx⟩, ?_⟩
      rintro ⟨hxzComp, hxyComp⟩
      apply hcross
      exact ⟨hxyComp.symm, hxyComp.symm.trans hxzComp⟩
  have hcomponentChoice (v : Fin 64) : v ∈ c.supp ∨ D.connectedComponentMk v = e := by
    rcases hcomponents (D.connectedComponentMk v) with hv | hv
    · exact Or.inl ((ConnectedComponent.mem_supp_iff c v).mpr hv)
    · exact Or.inr hv
  have hunique (p : Fin 64 × Fin 64 × Fin 64) (hp : p ∈ M) :
      (p.1 ∈ c.supp ∧ p.2.2 ∉ c.supp ∧ p.2.1 ∉ c.supp) ∨
      (p.1 ∉ c.supp ∧ p.2.2 ∈ c.supp ∧ p.2.1 ∉ c.supp) ∨
      (p.1 ∉ c.supp ∧ p.2.2 ∉ c.supp ∧ p.2.1 ∈ c.supp) := by
    have hp' := hp
    simp only [M, multiComponentAmbientCyclicTriangles,
      cyclicColoredTriples, Finset.mem_filter, Finset.mem_univ, true_and] at hp'
    rcases hp' with ⟨⟨hxy, hyz, hzx⟩, hcross⟩
    by_cases hx : p.1 ∈ c.supp
    · have hout := hinterior ⟨p.1, hx⟩ hxy hzx.symm hyz
      exact Or.inl ⟨hx, hout.1, hout.2⟩
    · by_cases hy : p.2.2 ∈ c.supp
      · have hout := hinterior ⟨p.2.2, hy⟩ hyz hxy.symm hzx
        exact Or.inr (Or.inl ⟨hx, hy, hout.1⟩)
      · have hz : p.2.1 ∈ c.supp := by
          rcases hcomponentChoice p.1 with hxc | hxe
          · exact (hx hxc).elim
          rcases hcomponentChoice p.2.2 with hyc | hye
          · exact (hy hyc).elim
          rcases hcomponentChoice p.2.1 with hzc | hze
          · exact hzc
          exfalso
          apply hcross
          exact ⟨hxe.trans hze.symm, hxe.trans hye.symm⟩
        exact Or.inr (Or.inr ⟨hx, hy, hz⟩)
  have hfirst :
      M.filter (fun p => p.1 ∈ c.supp) =
        cyclicColoredTriplesFirstRootIn G G G c.supp := by
    ext p
    simp only [M, multiComponentAmbientCyclicTriangles,
      cyclicColoredTriplesFirstRootIn, Finset.mem_filter]
    constructor
    · rintro ⟨⟨htri, _hcross⟩, hx⟩
      exact ⟨htri, hx⟩
    · rintro ⟨htri, hx⟩
      have ht := htri
      simp only [cyclicColoredTriples, Finset.mem_filter,
        Finset.mem_univ, true_and] at ht
      have hout := hinterior ⟨p.1, hx⟩ ht.1 ht.2.2.symm ht.2.1
      refine ⟨⟨htri, ?_⟩, hx⟩
      rintro ⟨hxzComp, hxyComp⟩
      have hxc := (ConnectedComponent.mem_supp_iff c p.1).mp hx
      exact hout.1 ((ConnectedComponent.mem_supp_iff c p.2.2).mpr
        (hxyComp.symm.trans hxc))
  have hfactor := card_eq_three_mul_card_filter_first_of_cyclic_unique
    M c.supp hrotate hunique
  rw [hfirst, card_cyclicColoredTriplesFirstRootIn_eq_sum_rooted,
    hroot96] at hfactor
  norm_num at hfactor ⊢
  exact hfactor

end

end Erdos85

#print axioms
  Erdos85.orderSixtyFour_sixTwo_allTf_multiComponentAmbient_card_eq_288
