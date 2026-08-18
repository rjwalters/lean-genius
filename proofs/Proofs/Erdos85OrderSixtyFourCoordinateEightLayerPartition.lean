import Proofs.Erdos85OrderSixtyFourCoordinateEightLayerFamily

/-! # Exact partition by the eight order-64 coordinate layers -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The six small layers and two distinguished-component layers exhaust every
row of the shared `8 × 8` coordinate grid exactly once. -/
theorem orderSixtyFour_seven_defect_components_coordinate_eightLayer_partition
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
              ∃ ρ : (Fin 6 ⊕ Fin 2) → (e.supp ≃ f.supp),
                (∀ i x, (secondOrderDefectGraph G).connectedComponentMk
                  (φ.symm (x, ρ (.inl i) x)) = (κ i).1) ∧
                (∀ j x, (secondOrderDefectGraph G).connectedComponentMk
                  (φ.symm (x, ρ (.inr j) x)) = c) ∧
                ∀ x, Function.Bijective (fun q => ρ q x) := by
  classical
  obtain ⟨c, hc16, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_coordinate_eightLayer_family
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  intro e hec
  obtain ⟨he8, hecoords⟩ := hsmall e hec
  refine ⟨he8, ?_⟩
  intro f hfc
  obtain ⟨hf8, hfcoords⟩ := hecoords f hfc
  refine ⟨hf8, ?_⟩
  intro hef
  obtain ⟨φ, κ, σ, τ₀, τ₁, hσcomp, hσdisj,
    hτ₀comp, hτ₁comp, hτdisj, hcross⟩ := hfcoords hef
  let τ : Fin 2 → (e.supp ≃ f.supp) :=
    Fin.cases τ₀ (fun _ => τ₁)
  let ρ : (Fin 6 ⊕ Fin 2) → (e.supp ≃ f.supp) :=
    Sum.elim σ τ
  refine ⟨φ, κ, ρ, ?_, ?_, ?_⟩
  · intro i x
    exact hσcomp i x
  · intro j x
    fin_cases j
    · exact hτ₀comp x
    · exact hτ₁comp x
  · intro x
    rw [Fintype.bijective_iff_injective_and_card]
    constructor
    · intro q₁ q₂ hq
      cases q₁ with
      | inl i =>
          cases q₂ with
          | inl j =>
              have hij : i = j := by
                by_contra hne
                exact hσdisj i j hne x hq
              exact congrArg Sum.inl hij
          | inr j =>
              fin_cases j
              · exact False.elim ((hcross i x).1 hq)
              · exact False.elim ((hcross i x).2 hq)
      | inr i =>
          cases q₂ with
          | inl j =>
              fin_cases i
              · exact False.elim ((hcross j x).1 hq.symm)
              · exact False.elim ((hcross j x).2 hq.symm)
          | inr j =>
              fin_cases i <;> fin_cases j
              · rfl
              · exact False.elim (hτdisj x hq)
              · exact False.elim (hτdisj x hq.symm)
              · rfl
    · rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
      have hfcard : Fintype.card f.supp = f.supp.ncard := by
        simpa [Nat.card_eq_fintype_card] using Nat.card_coe_set_eq f.supp
      omega

end

end Erdos85
