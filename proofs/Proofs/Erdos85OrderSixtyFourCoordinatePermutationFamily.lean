import Proofs.Erdos85OrderSixtyFourCoordinateLayerPermutations

/-! # The simultaneous family of six coordinate permutations -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The six small components give a simultaneous family of pointwise
distinct permutations between the two coordinate blocks. -/
theorem orderSixtyFour_seven_defect_components_coordinate_permutation_family
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
            ∃ σ : {k // k ≠ c} → (e.supp ≃ f.supp),
              (∀ k x,
                (secondOrderDefectGraph G).connectedComponentMk
                  (φ.symm (x, σ k x)) = k.1) ∧
              ∀ k l, k ≠ l → ∀ x, σ k x ≠ σ l x := by
  classical
  obtain ⟨c, hc16, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_coordinate_layer_permutations
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  intro e hec
  obtain ⟨he8, hecoords⟩ := hsmall e hec
  refine ⟨he8, ?_⟩
  intro f hfc
  obtain ⟨hf8, hfcoords⟩ := hecoords f hfc
  refine ⟨hf8, ?_⟩
  intro hef
  obtain ⟨φ, hperm⟩ := hfcoords hef
  let σ : {k // k ≠ c} → (e.supp ≃ f.supp) := fun k =>
    Classical.choose (hperm k.1 k.2)
  have hσ (k : {k // k ≠ c}) (x : e.supp) :
      (secondOrderDefectGraph G).connectedComponentMk
        (φ.symm (x, σ k x)) = k.1 :=
    Classical.choose_spec (hperm k.1 k.2) x
  refine ⟨φ, σ, hσ, ?_⟩
  intro k l hkl x heq
  apply hkl
  apply Subtype.ext
  calc
    k.1 = (secondOrderDefectGraph G).connectedComponentMk
        (φ.symm (x, σ k x)) := (hσ k x).symm
    _ = (secondOrderDefectGraph G).connectedComponentMk
        (φ.symm (x, σ l x)) := by rw [heq]
    _ = l.1 := hσ l x

end

end Erdos85
