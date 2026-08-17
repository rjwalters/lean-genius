import Proofs.Erdos85NonsquareComponentMultiplicityParity

/-!
# Nonsquare multiplicity patterns in the four-component order-64 branch

With exactly four defect components, Case B parity reduces the number of
components carrying odd multiplicity for a fixed defect eigenvalue to the
three possibilities `0`, `2`, or `4`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **Four-component Case B pattern trichotomy.** -/
theorem orderSixtyFour_fourComponent_nonsquare_oddMultiplicity_card
    {K : Type*} [Field K] [CharZero K]
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {μ : K} (hμ : μ ≠ (7 : K))
    (hnonsquare : ¬ IsSquare ((8 : K) - 1 - μ)) :
    let S := (Finset.univ : Finset
      (secondOrderDefectGraph G).ConnectedComponent).filter (fun c =>
        Odd (Module.finrank K
          (defectEigenspace
            (((secondOrderDefectGraph G).induce c.supp).adjMatrix K) μ)))
    Even S.card ∧ (S.card = 0 ∨ S.card = 2 ∨ S.card = 4) := by
  let D := secondOrderDefectGraph G
  let S := (Finset.univ : Finset D.ConnectedComponent).filter (fun c =>
    Odd (Module.finrank K
      (defectEigenspace ((D.induce c.supp).adjMatrix K) μ)))
  have hDreg : ∀ x, D.degree x = 5 + 2 := by
    intro x
    apply secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg (d := 8) (e := 5)
    norm_num
  have heven : Even S.card := by
    simpa [D, S] using
      graph_even_card_components_with_odd_multiplicity_of_regular_excess_field
        G hfree hreg hDreg hμ hnonsquare
  have hle : S.card ≤ 4 := by
    have hsub : S ⊆ (Finset.univ : Finset D.ConnectedComponent) :=
      Finset.filter_subset _ _
    have hc := Finset.card_le_card hsub
    have hcountD : Fintype.card D.ConnectedComponent = 4 := by
      simpa only [D] using hcount
    simpa [hcountD] using hc
  obtain ⟨k, hk⟩ := heven
  refine ⟨⟨k, hk⟩, ?_⟩
  rw [hk] at hle ⊢
  omega

end

end Erdos85
