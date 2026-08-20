import Proofs.Erdos85NegativeSignedJointEdgeIndexedServiceGraph
import Proofs.Erdos85OutsidePairEdgeEquivSemantics

/-! # Transporting the service equation to exterior-edge coordinates -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- The semantic outside-edge equivalence turns the ambient cross block into
the endpoint-incidence matrix and transports `H B + B C = J` verbatim. -/
theorem edgeIndexedServiceEquation_of_semantics
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (owner : OutsidePairEdgeEquivSemantics G c)
    (hcross :
      (G.induce c.supp).adjMatrix ℂ *
          (G.adjMatrix ℂ).toBlock (fun x ↦ x ∈ c.supp)
            (fun x ↦ x ∈ ({x | x ∉ c.supp} : Set (Fin 64))) +
        (G.adjMatrix ℂ).toBlock (fun x ↦ x ∈ c.supp)
            (fun x ↦ x ∈ ({x | x ∉ c.supp} : Set (Fin 64))) *
          (G.induce {x | x ∉ c.supp}).adjMatrix ℂ =
        (fun _ _ ↦ (1 : ℂ))) :
    let R := exteriorPairGraph G c.supp
    let Cg := G.induce {x | x ∉ c.supp}
    let Cedge : SimpleGraph R.edgeFinset := Cg.comap owner.equiv.symm
    EdgeIndexedServiceEquation (G.induce c.supp) R Cedge := by
  classical
  let R := exteriorPairGraph G c.supp
  let Cg := G.induce {x | x ∉ c.supp}
  let Cedge : SimpleGraph R.edgeFinset := Cg.comap owner.equiv.symm
  let B := (G.adjMatrix ℂ).toBlock (fun x ↦ x ∈ c.supp)
    (fun x ↦ x ∈ ({x | x ∉ c.supp} : Set (Fin 64)))
  let I := edgeEndpointIncidenceMatrix R
  have hBI : ∀ (u : c.supp) (a : R.edgeFinset),
      B u (owner.equiv.symm a) = I u a := by
    intro u a
    have hmem : u ∈ a.1.toFinset ↔ G.Adj u.1 (owner.equiv.symm a).1 := by
      simpa using owner.mem_edge_iff_adj (owner.equiv.symm a) u
    by_cases h : G.Adj u.1 (owner.equiv.symm a).1
    · have hm := hmem.mpr h
      simp [B, I, Matrix.toBlock_apply, edgeEndpointIncidenceMatrix,
        SimpleGraph.adjMatrix_apply, h, hm]
    · have hm := fun hu ↦ h (hmem.mp hu)
      simp [B, I, Matrix.toBlock_apply, edgeEndpointIncidenceMatrix,
        SimpleGraph.adjMatrix_apply, h, show u ∉ a.1.toFinset from hm]
  unfold EdgeIndexedServiceEquation
  funext u a
  have hc := congrFun (congrFun hcross u) (owner.equiv.symm a)
  simp only [Matrix.add_apply, Matrix.mul_apply] at hc ⊢
  calc
    (∑ y, (G.induce c.supp).adjMatrix ℂ u y * I y a) +
          ∑ b, I u b * Cedge.adjMatrix ℂ b a =
        (∑ y, (G.induce c.supp).adjMatrix ℂ u y *
            B y (owner.equiv.symm a)) +
          ∑ z, B u z * Cg.adjMatrix ℂ z (owner.equiv.symm a) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro y _
        rw [hBI]
      · symm
        apply Fintype.sum_equiv owner.equiv
        intro z
        have hb := hBI u (owner.equiv z)
        simp only [owner.equiv.symm_apply_apply] at hb
        rw [hb]
        simp [Cedge, Cg, SimpleGraph.adjMatrix_apply]
    _ = 1 := hc

/-- At regular order 64 there is a semantic edge-indexed service graph
satisfying the transported incidence equation. -/
theorem orderSixtyFour_exists_edgeIndexedServiceEquation
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x : Fin 64, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16) :
    ∃ owner : OutsidePairEdgeEquivSemantics G c,
      let R := exteriorPairGraph G c.supp
      let Cg := G.induce {x | x ∉ c.supp}
      let Cedge : SimpleGraph R.edgeFinset := Cg.comap owner.equiv.symm
      EdgeIndexedServiceEquation (G.induce c.supp) R Cedge := by
  classical
  obtain ⟨owner⟩ := exists_outsidePairEdgeEquivSemantics G hfree hreg c hc
  obtain ⟨_label, _hqcard, _hcard, _hinc, _himage, _hRreg, _hRedges,
      _hCgReg, _hCgFree, hcross⟩ :=
    orderSixtyFour_regular_sizeSixteen_outsidePair_feasibility
      G hfree hreg c hc
  exact ⟨owner, edgeIndexedServiceEquation_of_semantics G c owner hcross⟩

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_exists_edgeIndexedServiceEquation
