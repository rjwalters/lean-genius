import Proofs.Erdos85OrderSixtyFourCoordinatePermutationFamily

/-! # A Fin 6 indexing of the small coordinate layers -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The six small components and their pointwise-disjoint coordinate
permutations can be labeled by `Fin 6`. -/
theorem orderSixtyFour_seven_defect_components_coordinate_finSix_family
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16 ∧
      ∀ e, e ≠ c → e.supp.ncard = 8 ∧
        ∀ f, f ≠ c → f.supp.ncard = 8 ∧
          ∀ (_hef : e ≠ f), ∃ φ : Fin 64 ≃ e.supp × f.supp,
            ∃ κ : Fin 6 ≃ {k // k ≠ c},
              ∃ σ : Fin 6 → (e.supp ≃ f.supp),
                (∀ i x,
                  (secondOrderDefectGraph G).connectedComponentMk
                    (φ.symm (x, σ i x)) = (κ i).1) ∧
                ∀ i j, i ≠ j → ∀ x, σ i x ≠ σ j x := by
  classical
  obtain ⟨c, hc16, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_coordinate_permutation_family
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  intro e hec
  obtain ⟨he8, hecoords⟩ := hsmall e hec
  refine ⟨he8, ?_⟩
  intro f hfc
  obtain ⟨hf8, hfcoords⟩ := hecoords f hfc
  refine ⟨hf8, ?_⟩
  intro hef
  obtain ⟨φ, σK, hσK, hdisjK⟩ := hfcoords hef
  let K := {k : (secondOrderDefectGraph G).ConnectedComponent // k ≠ c}
  have hKcard : Fintype.card K = 6 := by
    rw [Fintype.card_subtype_compl
      (fun k : (secondOrderDefectGraph G).ConnectedComponent => k = c), hcount]
    simp
  let κ : Fin 6 ≃ K :=
    (finCongr hKcard.symm).trans (Fintype.equivFin K).symm
  let σ : Fin 6 → (e.supp ≃ f.supp) := fun i => σK (κ i)
  refine ⟨φ, κ, σ, ?_, ?_⟩
  · intro i x
    exact hσK (κ i) x
  · intro i j hij x
    apply hdisjK (κ i) (κ j)
    exact fun h => hij (κ.injective h)

end

end Erdos85
