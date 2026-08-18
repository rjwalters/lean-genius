import Proofs.Erdos85OrderSixtyFourCoordinateSmallLayers

/-! # Permutations representing the six small coordinate layers -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Each order-eight defect component is the graph of a permutation between
the two coordinate blocks. -/
theorem orderSixtyFour_seven_defect_components_coordinate_layer_permutations
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
            ∀ k, k ≠ c → ∃ σ : e.supp ≃ f.supp,
              ∀ x : e.supp,
                (secondOrderDefectGraph G).connectedComponentMk
                  (φ.symm (x, σ x)) = k := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_coordinate_smallLayer_degrees
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  intro e hec
  obtain ⟨he8, hecoords⟩ := hsmall e hec
  refine ⟨he8, ?_⟩
  intro f hfc
  obtain ⟨hf8, hfcoords⟩ := hecoords f hfc
  refine ⟨hf8, ?_⟩
  intro hef
  obtain ⟨φ, hlayers⟩ := hfcoords hef
  refine ⟨φ, ?_⟩
  intro k hkc
  obtain ⟨_hk8, hrow, hcol⟩ := hlayers k hkc
  let R (x : e.supp) : Finset (Fin 64) :=
    Finset.univ.filter fun z => D.connectedComponentMk z = k ∧ (φ z).1 = x
  let C (y : f.supp) : Finset (Fin 64) :=
    Finset.univ.filter fun z => D.connectedComponentMk z = k ∧ (φ z).2 = y
  have hRcard (x : e.supp) : (R x).card = 1 := hrow x
  have hCcard (y : f.supp) : (C y).card = 1 := hcol y
  let zOf (x : e.supp) : Fin 64 :=
    Classical.choose (Finset.card_eq_one.mp (hRcard x))
  have hzOf_mem (x : e.supp) : zOf x ∈ R x := by
    have hs := Classical.choose_spec (Finset.card_eq_one.mp (hRcard x))
    rw [hs]
    simp [zOf]
  have hzOf_comp (x : e.supp) : D.connectedComponentMk (zOf x) = k :=
    (Finset.mem_filter.mp (hzOf_mem x)).2.1
  have hzOf_row (x : e.supp) : (φ (zOf x)).1 = x :=
    (Finset.mem_filter.mp (hzOf_mem x)).2.2
  let σfun : e.supp → f.supp := fun x => (φ (zOf x)).2
  have hσinj : Function.Injective σfun := by
    intro x₁ x₂ hσ
    let y := σfun x₁
    have hz₁C : zOf x₁ ∈ C y := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hzOf_comp x₁, rfl⟩
    have hz₂C : zOf x₂ ∈ C y := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hzOf_comp x₂, hσ.symm⟩
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp (hCcard y)
    rw [hz] at hz₁C hz₂C
    have hz₁ : zOf x₁ = z := by simpa using hz₁C
    have hz₂ : zOf x₂ = z := by simpa using hz₂C
    have hz12 : zOf x₁ = zOf x₂ := hz₁.trans hz₂.symm
    calc
      x₁ = (φ (zOf x₁)).1 := (hzOf_row x₁).symm
      _ = (φ (zOf x₂)).1 := congrArg (fun z => (φ z).1) hz12
      _ = x₂ := hzOf_row x₂
  have hσsurj : Function.Surjective σfun := by
    intro y
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp (hCcard y)
    have hzC : z ∈ C y := by rw [hz]; simp
    let x : e.supp := (φ z).1
    have hzR : z ∈ R x := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hzC).2.1, rfl⟩
    have hzOfR : zOf x ∈ R x := hzOf_mem x
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp (hRcard x)
    rw [hw] at hzR hzOfR
    have hzOfEq : zOf x = w := by simpa using hzOfR
    have hzEq : z = w := by simpa using hzR
    have heq : zOf x = z := hzOfEq.trans hzEq.symm
    refine ⟨x, ?_⟩
    change (φ (zOf x)).2 = y
    rw [heq]
    exact (Finset.mem_filter.mp hzC).2.2
  let σ : e.supp ≃ f.supp := Equiv.ofBijective σfun ⟨hσinj, hσsurj⟩
  refine ⟨σ, ?_⟩
  intro x
  have hpair : φ (zOf x) = (x, σ x) := by
    apply Prod.ext
    · exact hzOf_row x
    · rfl
  have hinv := congrArg φ.symm hpair
  have hzEq : zOf x = φ.symm (x, σ x) := by simpa using hinv
  rw [← hzEq]
  exact hzOf_comp x

end

end Erdos85
