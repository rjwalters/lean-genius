import Proofs.Erdos85OrderSixtyFourRoutingCycleConcentrationTerminal

/-! # Separation of prescribed cycles from monochromatic routing lifts -/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 10000 in
/-- A prescribed `(a,b,c)` routing cycle and the two monochromatic `c,c`
lifts of its closing `c`-route use disjoint middle vertices. -/
theorem rootedRoutingCycle_monochromaticClosingLifts_card_two_and_avoid_middle
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    {a b c e f : (secondOrderDefectGraph G).ConnectedComponent}
    (hac : a ≠ c)
    (x : Fin 64) (p : Fin 64 × Fin 64)
    (hp : p ∈ rootedAllDistinctRoutingCyclePairsInComponents
      G hfree a b c e f x)
    (hallTwo : ∀ c d e f :
      (secondOrderDefectGraph G).ConnectedComponent,
      ∀ (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f),
      ∀ (x : c.supp) (w : f.supp),
        d = crossIntermediateComponent G hfree hcf x w →
        ((Finset.univ : Finset e.supp).filter fun z =>
          d = crossIntermediateComponent G hfree hce x z ∧
            d = crossIntermediateComponent G hfree hef z w).card = 2) :
    let D := secondOrderDefectGraph G
    let d := D.connectedComponentMk x
    ∃ (hde : d ≠ e) (hef : e ≠ f) (hdf : d ≠ f),
      let xs : d.supp := ⟨x, ConnectedComponent.connectedComponentMk_mem⟩
      let ys : e.supp := ⟨p.2, by
        exact (ConnectedComponent.mem_supp_iff e p.2).mpr
          (Finset.mem_filter.mp hp).2.1⟩
      let zs : f.supp := ⟨p.1, by
        exact (ConnectedComponent.mem_supp_iff f p.1).mpr
          (Finset.mem_filter.mp hp).2.2⟩
      let L := (Finset.univ : Finset e.supp).filter fun z =>
        c = crossIntermediateComponent G hfree hde xs z ∧
          c = crossIntermediateComponent G hfree hef z zs
      L.card = 2 ∧ ys ∉ L ∧ (insert ys L).card = 3 := by
  classical
  let D := secondOrderDefectGraph G
  have hpcomp := (Finset.mem_filter.mp hp).2
  have hroute := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  obtain ⟨hxy, hyz, hzx, ha, _hb, hc⟩ := hroute
  have heq : D.connectedComponentMk p.2 = e := hpcomp.1
  have hfeq : D.connectedComponentMk p.1 = f := hpcomp.2
  subst e
  subst f
  let d := D.connectedComponentMk x
  have hde : d ≠ D.connectedComponentMk p.2 := by
    simpa only [d] using hxy
  have hef : D.connectedComponentMk p.2 ≠ D.connectedComponentMk p.1 := hyz
  have hdf : d ≠ D.connectedComponentMk p.1 := by
    simpa only [d] using hzx.symm
  let xs : d.supp := ⟨x, ConnectedComponent.connectedComponentMk_mem⟩
  let ys : (D.connectedComponentMk p.2).supp := ⟨p.2,
    ConnectedComponent.connectedComponentMk_mem⟩
  let zs : (D.connectedComponentMk p.1).supp := ⟨p.1,
    ConnectedComponent.connectedComponentMk_mem⟩
  let L := (Finset.univ : Finset (D.connectedComponentMk p.2).supp).filter fun z =>
    c = crossIntermediateComponent G hfree hde xs z ∧
      c = crossIntermediateComponent G hfree hef z zs
  have hdirect : c = crossIntermediateComponent G hfree hdf xs zs := by
    rw [crossIntermediateComponent_reverse G hfree hdf xs zs]
    simpa [D, d, xs, zs] using hc.symm
  have hLcard : L.card = 2 := by
    exact hallTwo d c (D.connectedComponentMk p.2)
      (D.connectedComponentMk p.1) hde hef hdf xs zs hdirect
  have hys : ys ∉ L := by
    intro hys
    have hcy := (Finset.mem_filter.mp hys).2.1
    have hca : c = a := by
      calc
        c = crossIntermediateComponent G hfree hde xs ys := hcy
        _ = a := by
          simpa only using ha
    exact hac hca.symm
  refine ⟨hde, hef, hdf, hLcard, hys, ?_⟩
  rw [Finset.card_insert_of_notMem hys, hLcard]

end

end Erdos85
