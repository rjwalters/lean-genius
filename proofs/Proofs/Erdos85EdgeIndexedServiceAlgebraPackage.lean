import Proofs.Erdos85EdgeIndexedServiceSquaredEquation

/-! # Unified algebraic package for the order-64 edge service graph -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- One semantic owner equivalence simultaneously supplies the service
equation, 6-regularity, `C₄`-freeness, and the instantiated squared equation.
This avoids choosing unrelated reindexings for the combinatorial and
algebraic service models. -/
theorem orderSixtyFour_exists_edgeIndexedServiceAlgebraPackage
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x : Fin 64, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16) :
    ∃ owner : OutsidePairEdgeEquivSemantics G c,
      let H := G.induce c.supp
      let R := exteriorPairGraph G c.supp
      let Cg := G.induce {x | x ∉ c.supp}
      let Cedge : SimpleGraph R.edgeFinset := Cg.comap owner.equiv.symm
      EdgeIndexedServiceEquation H R Cedge ∧
      (∀ a, Cedge.degree a = 6) ∧
      ¬ containsC4 R.edgeFinset Cedge ∧
      H.adjMatrix ℂ * H.adjMatrix ℂ * edgeEndpointIncidenceMatrix R -
          edgeEndpointIncidenceMatrix R * Cedge.adjMatrix ℂ *
            Cedge.adjMatrix ℂ =
        (-4 : ℂ) • edgeIndexedOnesMatrix R := by
  classical
  obtain ⟨owner, hservice⟩ :=
    orderSixtyFour_exists_edgeIndexedServiceEquation G hfree hreg c hc
  let H := G.induce c.supp
  let R := exteriorPairGraph G c.supp
  let Cg := G.induce {x | x ∉ c.supp}
  let Cedge : SimpleGraph R.edgeFinset := Cg.comap owner.equiv.symm
  obtain ⟨_label, _hqcard, _hcard, _hinc, _himage, _hRreg, _hRedges,
      hCgReg, hCgFree, _hcross⟩ :=
    orderSixtyFour_regular_sizeSixteen_outsidePair_feasibility
      G hfree hreg c hc
  have hCreg : ∀ a, Cedge.degree a = 6 := by
    intro a
    calc
      Cedge.degree a = Cg.degree (owner.equiv.symm a) := by
        rw [← SimpleGraph.card_neighborSet_eq_degree,
          ← SimpleGraph.card_neighborSet_eq_degree]
        exact Fintype.card_congr
          ((SimpleGraph.Iso.comap owner.equiv.symm Cg).mapNeighborSet a)
      _ = 6 := hCgReg (owner.equiv.symm a)
  have hCfree : ¬ containsC4 R.edgeFinset Cedge := by
    intro hcycle
    rcases hcycle with ⟨f, hf, hadj⟩
    apply hCgFree
    refine ⟨owner.equiv.symm ∘ f, owner.equiv.symm.injective.comp hf, ?_⟩
    intro i j hij
    exact hadj i j hij
  have hHreg : ∀ z : c.supp, H.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg (by norm_num) c (m := 2)
        (by simpa using hc) z
  have hsq := edgeIndexedService_squaredEquation_of_regular
    H R Cedge hservice 2 6 hHreg hCreg
  refine ⟨owner, hservice, hCreg, hCfree, ?_⟩
  norm_num at hsq
  simpa [neg_smul, H, R, Cg, Cedge] using hsq

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_exists_edgeIndexedServiceAlgebraPackage
