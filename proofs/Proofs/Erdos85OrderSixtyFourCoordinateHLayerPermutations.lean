import Proofs.Erdos85OrderSixtyFourCoordinateHLayer
import Proofs.Erdos85TwoBiregularDecomposition

/-! # Splitting the H16 coordinate layer into two permutations -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The two-regular H16 grid layer is the disjoint union of two permutation
graphs between the coordinate blocks. -/
theorem orderSixtyFour_seven_defect_components_coordinate_HLayer_permutations
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
            ∃ τ₀ τ₁ : e.supp ≃ f.supp,
              (∀ x, (secondOrderDefectGraph G).connectedComponentMk
                (φ.symm (x, τ₀ x)) = c) ∧
              (∀ x, (secondOrderDefectGraph G).connectedComponentMk
                (φ.symm (x, τ₁ x)) = c) ∧
              ∀ x, τ₀ x ≠ τ₁ x := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_coordinate_HLayer_degrees
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  intro e hec
  obtain ⟨he8, hecoords⟩ := hsmall e hec
  refine ⟨he8, ?_⟩
  intro f hfc
  obtain ⟨hf8, hfcoords⟩ := hecoords f hfc
  refine ⟨hf8, ?_⟩
  intro hef
  obtain ⟨φ, hrow, hcol⟩ := hfcoords hef
  let t : e.supp → Finset f.supp := fun x =>
    Finset.univ.filter fun y => D.connectedComponentMk (φ.symm (x, y)) = c
  have ht : HallsTheoremOQ01OQ03.IsBiregular t 2 := by
    constructor
    · intro x
      let S : Finset (Fin 64) :=
        Finset.univ.filter fun z => D.connectedComponentMk z = c ∧ (φ z).1 = x
      calc
        (t x).card = S.card := by
          apply Finset.card_bij (fun y _ => φ.symm (x, y))
          · intro y hy
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2, ?_⟩
            simp
          · intro y₁ _ y₂ _ h
            have hp := φ.symm.injective h
            exact congrArg Prod.snd hp
          · intro z hz
            let y : f.supp := (φ z).2
            have hpair : (x, y) = φ z := by
              apply Prod.ext
              · exact (Finset.mem_filter.mp hz).2.2.symm
              · rfl
            have hmap : φ.symm (x, y) = z := by
              calc
                φ.symm (x, y) = φ.symm (φ z) := congrArg φ.symm hpair
                _ = z := φ.symm_apply_apply z
            refine ⟨y, ?_, ?_⟩
            · apply Finset.mem_filter.mpr
              refine ⟨Finset.mem_univ _, ?_⟩
              have hzcomp := (Finset.mem_filter.mp hz).2.1
              rw [hmap]
              exact hzcomp
            · exact hmap
        _ = 2 := hrow x
    · intro y
      let S : Finset (Fin 64) :=
        Finset.univ.filter fun z => D.connectedComponentMk z = c ∧ (φ z).2 = y
      calc
        ((Finset.univ : Finset e.supp).filter fun x => y ∈ t x).card = S.card := by
          apply Finset.card_bij (fun x _ => φ.symm (x, y))
          · intro x hx
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_univ _, ?_, by simp⟩
            exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).2).2
          · intro x₁ _ x₂ _ h
            have hp := φ.symm.injective h
            exact congrArg Prod.fst hp
          · intro z hz
            let x : e.supp := (φ z).1
            have hpair : (x, y) = φ z := by
              apply Prod.ext
              · rfl
              · exact (Finset.mem_filter.mp hz).2.2.symm
            have hmap : φ.symm (x, y) = z := by
              calc
                φ.symm (x, y) = φ.symm (φ z) := congrArg φ.symm hpair
                _ = z := φ.symm_apply_apply z
            refine ⟨x, ?_, ?_⟩
            · apply Finset.mem_filter.mpr
              refine ⟨Finset.mem_univ _, ?_⟩
              apply Finset.mem_filter.mpr
              refine ⟨Finset.mem_univ _, ?_⟩
              have hzcomp := (Finset.mem_filter.mp hz).2.1
              rw [hmap]
              exact hzcomp
            · exact hmap
        _ = 2 := hcol y
  obtain ⟨τ₀, τ₁, hτ₀, hτ₁, hdisj⟩ :=
    exists_two_disjoint_equiv_of_two_biregular t ht
  refine ⟨φ, τ₀, τ₁, ?_, ?_, hdisj⟩
  · intro x
    exact (Finset.mem_filter.mp (hτ₀ x)).2
  · intro x
    exact (Finset.mem_filter.mp (hτ₁ x)).2

end

end Erdos85
