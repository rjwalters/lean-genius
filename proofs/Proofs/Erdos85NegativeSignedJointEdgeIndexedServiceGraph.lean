import Proofs.Erdos85NegativeSignedJointOutsidePairEncoding

/-! # The outside service graph in exterior-edge coordinates -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Endpoint incidence matrix of a graph, with columns indexed by its edges. -/
def edgeEndpointIncidenceMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] : Matrix V R.edgeFinset ℂ :=
  fun x e ↦ if x ∈ e.1.toFinset then 1 else 0

/-- The exact service identity still to be discharged after transporting the
outside block through its canonical equivalence with the exterior edges. -/
def EdgeIndexedServiceEquation
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj] : Prop :=
  H.adjMatrix ℂ * edgeEndpointIncidenceMatrix R +
      edgeEndpointIncidenceMatrix R * Cedge.adjMatrix ℂ =
    fun _ _ ↦ 1

/-- The 48-vertex outside graph can be reindexed canonically by the 48 edges
of the exterior-pair graph.  In these incidence coordinates it remains
six-regular and `C₄`-free. -/
theorem orderSixtyFour_exists_edgeIndexedServiceGraph
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x : Fin 64, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16) :
    let R := exteriorPairGraph G c.supp
    let Cg := G.induce {x | x ∉ c.supp}
    ∃ (e : {x : Fin 64 // x ∉ c.supp} ≃ R.edgeFinset),
      let Cedge : SimpleGraph R.edgeFinset := Cg.comap e.symm
      (∀ a b, Cedge.Adj a b ↔ Cg.Adj (e.symm a) (e.symm b)) ∧
      (∀ a, Cedge.degree a = 6) ∧
      ¬ containsC4 R.edgeFinset Cedge := by
  classical
  let R := exteriorPairGraph G c.supp
  let Cg := G.induce {x | x ∉ c.supp}
  obtain ⟨e⟩ := orderSixtyFour_regular_sizeSixteen_exists_outsidePairEdgeEquiv
    G hfree hreg c hc
  let Cedge : SimpleGraph R.edgeFinset := Cg.comap e.symm
  obtain ⟨_label, _hqcard, _hcard, _hinc, _himage, _hRreg, _hRedges,
      hCgReg, hCgFree, _hcross⟩ :=
    orderSixtyFour_regular_sizeSixteen_outsidePair_feasibility
      G hfree hreg c hc
  refine ⟨e, ?_, ?_, ?_⟩
  · intro a b
    rfl
  · intro a
    rw [← hCgReg (e.symm a)]
    rw [SimpleGraph.degree, SimpleGraph.degree]
    apply Finset.card_bij (fun b _ ↦ e.symm b)
    · intro b hb
      simpa [Cedge] using hb
    · intro b _ d _ hbd
      exact e.symm.injective hbd
    · intro z hz
      refine ⟨e z, by simpa [Cedge] using hz, by simp⟩
  · intro hcycle
    rcases hcycle with ⟨f, hf, hadj⟩
    apply hCgFree
    refine ⟨e.symm ∘ f, e.symm.injective.comp hf, ?_⟩
    intro i j hij
    exact hadj i j hij

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_exists_edgeIndexedServiceGraph
