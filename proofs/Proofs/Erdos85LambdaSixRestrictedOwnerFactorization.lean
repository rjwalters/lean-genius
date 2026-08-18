import Proofs.Erdos85LambdaSixGraphFourFactorization
import Proofs.Erdos85RestrictedOwnerCommutesInducedDefect
import Proofs.Erdos85RoutingOwnerRainbowExactColors

/-! # The four restricted owner graphs form the lambda-six factorization -/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem orderSixtyFour_restrictedOwners_graphFourFactorization
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hsize : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16)
    (owners : Fin 4 ≃ (secondOrderDefectGraph G).ConnectedComponent)
    (source : (secondOrderDefectGraph G).ConnectedComponent) :
    GraphFourFactorization
      ((secondOrderDefectGraph G).induce source.supp)
      (restrictedComponentOwnerGraph G source (owners 0))
      (restrictedComponentOwnerGraph G source (owners 1))
      (restrictedComponentOwnerGraph G source (owners 2))
      (restrictedComponentOwnerGraph G source (owners 3)) := by
  let D := secondOrderDefectGraph G
  let DL := D.induce source.supp
  let F : Fin 4 → SimpleGraph source.supp := fun i =>
    restrictedComponentOwnerGraph G source (owners i)
  have hdeg : ∀ i x, (F i).degree x = 2 := by
    intro i x
    exact binarySquare_regular_twoSizeTwoParts_restrictedOwner_degree_two
      G hfree (q := 8) (by omega) hreg (by norm_num) source (owners i)
      (by norm_num; exact hsize source)
      (by norm_num; exact hsize (owners i)) x
  have hcomm : ∀ i,
      (F i).adjMatrix ℤ * DL.adjMatrix ℤ =
        DL.adjMatrix ℤ * (F i).adjMatrix ℤ := by
    intro i
    exact orderSixtyFour_restrictedOwner_adjMatrix_comm_inducedDefect
      G hfree hreg source (owners i) (hsize (owners i))
  have hdisjoint : ∀ i x y, (F i).Adj x y → ¬DL.Adj x y := by
    intro i x y hF hD
    have hglobal :
        (componentOwnerGraph G D (owners i)).Adj x.1 y.1 := hF
    have hxy : x.1 ≠ y.1 := hglobal.1
    have hnotD : ¬D.Adj x.1 y.1 :=
      (not_secondOrderDefect_adj_iff_existsUnique_componentOwnerGraph_adj
        G hfree hxy).mpr ⟨owners i, hglobal, by
          intro c hc
          exact (componentOwnerGraph_adj_iff_owner_eq_of_adj
            G hfree (owners i) hglobal c).mp hc⟩
    exact hnotD hD
  refine ⟨hdeg 0, hdeg 1, hdeg 2, hdeg 3,
    hdisjoint 0, hdisjoint 1, hdisjoint 2, hdisjoint 3,
    hcomm 0, hcomm 1, hcomm 2, hcomm 3, ?_⟩
  intro x y hxy
  split <;> rename_i hD
  · exact ⟨fun h => hdisjoint 0 x y h hD,
      fun h => hdisjoint 1 x y h hD,
      fun h => hdisjoint 2 x y h hD,
      fun h => hdisjoint 3 x y h hD⟩
  · have hxyval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
    have hnotD : ¬D.Adj x.1 y.1 := by
      simpa [DL, D, SimpleGraph.induce_adj] using hD
    obtain ⟨c, hc, hcuniq⟩ :=
      (not_secondOrderDefect_adj_iff_existsUnique_componentOwnerGraph_adj
        G hfree hxyval).mp hnotD
    generalize hiDef : owners.symm c = i
    have hi : owners i = c := by
      rw [← hiDef]
      exact owners.apply_symm_apply c
    have hFi : (F i).Adj x y := by
      change (componentOwnerGraph G D (owners i)).Adj x.1 y.1
      rw [hi]
      exact hc
    have hother : ∀ j : Fin 4, j ≠ i → ¬(F j).Adj x y := by
      intro j hji hj
      have hjglobal : (componentOwnerGraph G D (owners j)).Adj x.1 y.1 := hj
      have heq : owners j = c := hcuniq (owners j) hjglobal
      exact hji (owners.injective (heq.trans hi.symm))
    fin_cases i
    · exact Or.inl ⟨hFi, hother 1 (by decide), hother 2 (by decide),
        hother 3 (by decide)⟩
    · exact Or.inr (Or.inl ⟨hother 0 (by decide), hFi,
        hother 2 (by decide), hother 3 (by decide)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hother 0 (by decide),
        hother 1 (by decide), hFi, hother 3 (by decide)⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hother 0 (by decide),
        hother 1 (by decide), hother 2 (by decide), hFi⟩))

theorem orderSixtyFour_restrictedOwners_lambdaSixBoolFourFactorization
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hsize : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16)
    (owners : Fin 4 ≃ (secondOrderDefectGraph G).ConnectedComponent)
    (source : (secondOrderDefectGraph G).ConnectedComponent)
    (label : source.supp ≃ Fin 16) :
    LambdaSixBoolFourFactorization
      (relabeledGraphBool label
        ((secondOrderDefectGraph G).induce source.supp))
      (relabeledGraphBool label
        (restrictedComponentOwnerGraph G source (owners 0)))
      (relabeledGraphBool label
        (restrictedComponentOwnerGraph G source (owners 1)))
      (relabeledGraphBool label
        (restrictedComponentOwnerGraph G source (owners 2)))
      (relabeledGraphBool label
        (restrictedComponentOwnerGraph G source (owners 3))) := by
  apply graph_fourFactorization_relabel
  exact orderSixtyFour_restrictedOwners_graphFourFactorization
    G hfree hreg hsize owners source

end

end Erdos85
