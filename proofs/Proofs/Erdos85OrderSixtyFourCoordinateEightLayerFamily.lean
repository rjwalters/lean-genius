import Proofs.Erdos85OrderSixtyFourSmallBlockCoordinateCharacterization
import Proofs.Erdos85OneRegularGridPermutation
import Proofs.Erdos85TwoRegularGridPermutations

/-! # All eight order-64 coordinate layers over one grid -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem row_filter_card_eq_vertex_filter_card
    {V ι α : Type*} [Fintype V] [Fintype ι] [Fintype α]
    [DecidableEq V] [DecidableEq ι] [DecidableEq α]
    (φ : V ≃ ι × α) (p : V → Prop) [DecidablePred p] (x : ι) :
    ((Finset.univ : Finset α).filter fun y => p (φ.symm (x, y))).card =
      ((Finset.univ : Finset V).filter fun z => p z ∧ (φ z).1 = x).card := by
  apply Finset.card_bij (fun y _ => φ.symm (x, y))
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact ⟨hy, by simp⟩
  · intro y₁ hy₁ y₂ hy₂ h
    exact congrArg Prod.snd (φ.symm.injective h)
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    refine ⟨(φ z).2, ?_, ?_⟩
    · have hzx : φ.symm (x, (φ z).2) = z := by
        calc
          φ.symm (x, (φ z).2) = φ.symm (φ z) :=
            congrArg φ.symm (Prod.ext hz.2.symm rfl)
          _ = z := φ.symm_apply_apply z
      simpa [hzx] using hz.1
    · calc
        φ.symm (x, (φ z).2) = φ.symm (φ z) :=
          congrArg φ.symm (Prod.ext hz.2.symm rfl)
        _ = z := φ.symm_apply_apply z

private theorem column_filter_card_eq_vertex_filter_card
    {V ι α : Type*} [Fintype V] [Fintype ι] [Fintype α]
    [DecidableEq V] [DecidableEq ι] [DecidableEq α]
    (φ : V ≃ ι × α) (p : V → Prop) [DecidablePred p] (y : α) :
    ((Finset.univ : Finset ι).filter fun x => p (φ.symm (x, y))).card =
      ((Finset.univ : Finset V).filter fun z => p z ∧ (φ z).2 = y).card := by
  apply Finset.card_bij (fun x _ => φ.symm (x, y))
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨hx, by simp⟩
  · intro x₁ hx₁ x₂ hx₂ h
    exact congrArg Prod.fst (φ.symm.injective h)
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    refine ⟨(φ z).1, ?_, ?_⟩
    · have hzy : φ.symm ((φ z).1, y) = z := by
        calc
          φ.symm ((φ z).1, y) = φ.symm (φ z) :=
            congrArg φ.symm (Prod.ext rfl hz.2.symm)
          _ = z := φ.symm_apply_apply z
      simpa [hzy] using hz.1
    · calc
        φ.symm ((φ z).1, y) = φ.symm (φ z) :=
          congrArg φ.symm (Prod.ext rfl hz.2.symm)
        _ = z := φ.symm_apply_apply z

/-- For any two distinct small defect components, one coordinate equivalence
simultaneously exhibits all six small components and the distinguished
order-16 component as eight pairwise-disjoint permutation layers. -/
theorem orderSixtyFour_seven_defect_components_coordinate_eightLayer_family
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
                ∃ τ₀ τ₁ : e.supp ≃ f.supp,
                  (∀ i x, (secondOrderDefectGraph G).connectedComponentMk
                    (φ.symm (x, σ i x)) = (κ i).1) ∧
                  (∀ i j, i ≠ j → ∀ x, σ i x ≠ σ j x) ∧
                  (∀ x, (secondOrderDefectGraph G).connectedComponentMk
                    (φ.symm (x, τ₀ x)) = c) ∧
                  (∀ x, (secondOrderDefectGraph G).connectedComponentMk
                    (φ.symm (x, τ₁ x)) = c) ∧
                  (∀ x, τ₀ x ≠ τ₁ x) ∧
                  ∀ i x, σ i x ≠ τ₀ x ∧ σ i x ≠ τ₁ x := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_smallBlock_coordinate_iff
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  intro e hec
  obtain ⟨he8, hecoords⟩ := hsmall e hec
  refine ⟨he8, ?_⟩
  intro f hfc
  obtain ⟨hf8, hfcoords⟩ := hecoords f hfc
  refine ⟨hf8, ?_⟩
  intro hef
  obtain ⟨φ, hE, hF⟩ := hfcoords hef
  have hvertexRow (k : D.ConnectedComponent) (x : e.supp) :
      ((Finset.univ : Finset (Fin 64)).filter fun z =>
        D.connectedComponentMk z = k ∧ (φ z).1 = x).card =
        (componentNeighborFinset G D k x.1).card := by
    have heq :
        ((Finset.univ : Finset (Fin 64)).filter fun z =>
          D.connectedComponentMk z = k ∧ (φ z).1 = x) =
          componentNeighborFinset G D k x.1 := by
      ext z
      simp [componentNeighborFinset, D, hE z x, eq_comm, and_comm]
    exact congrArg Finset.card heq
  have hvertexCol (k : D.ConnectedComponent) (y : f.supp) :
      ((Finset.univ : Finset (Fin 64)).filter fun z =>
        D.connectedComponentMk z = k ∧ (φ z).2 = y).card =
        (componentNeighborFinset G D k y.1).card := by
    have heq :
        ((Finset.univ : Finset (Fin 64)).filter fun z =>
          D.connectedComponentMk z = k ∧ (φ z).2 = y) =
          componentNeighborFinset G D k y.1 := by
      ext z
      simp [componentNeighborFinset, D, hF z y, eq_comm, and_comm]
    exact congrArg Finset.card heq
  have hcomponentCard (k : D.ConnectedComponent) :
      k ≠ c → k.supp.ncard = 8 := by
    intro hkc
    exact (hsmall k hkc).1
  have hsmallRow (k : D.ConnectedComponent) (hkc : k ≠ c) (x : e.supp) :
      ((Finset.univ : Finset f.supp).filter fun y =>
        D.connectedComponentMk (φ.symm (x, y)) = k).card = 1 := by
    rw [row_filter_card_eq_vertex_filter_card φ
      (fun z => D.connectedComponentMk z = k) x]
    rw [hvertexRow]
    have h := orderSixtyFour_eight_mul_componentNeighborFinset_card
      G hfree hmin hcover k x.1
    have hk8 := hcomponentCard k hkc
    have : 8 * (componentNeighborFinset G D k x.1).card = 8 := by
      simpa [D, hk8] using h
    omega
  have hsmallCol (k : D.ConnectedComponent) (hkc : k ≠ c) (y : f.supp) :
      ((Finset.univ : Finset e.supp).filter fun x =>
        D.connectedComponentMk (φ.symm (x, y)) = k).card = 1 := by
    rw [column_filter_card_eq_vertex_filter_card φ
      (fun z => D.connectedComponentMk z = k) y]
    rw [hvertexCol]
    have h := orderSixtyFour_eight_mul_componentNeighborFinset_card
      G hfree hmin hcover k y.1
    have hk8 := hcomponentCard k hkc
    have : 8 * (componentNeighborFinset G D k y.1).card = 8 := by
      simpa [D, hk8] using h
    omega
  have hHRow (x : e.supp) :
      ((Finset.univ : Finset f.supp).filter fun y =>
        D.connectedComponentMk (φ.symm (x, y)) = c).card = 2 := by
    rw [row_filter_card_eq_vertex_filter_card φ
      (fun z => D.connectedComponentMk z = c) x]
    rw [hvertexRow]
    have h := orderSixtyFour_eight_mul_componentNeighborFinset_card
      G hfree hmin hcover c x.1
    have : 8 * (componentNeighborFinset G D c x.1).card = 16 := by
      simpa [D, hc16] using h
    omega
  have hHCol (y : f.supp) :
      ((Finset.univ : Finset e.supp).filter fun x =>
        D.connectedComponentMk (φ.symm (x, y)) = c).card = 2 := by
    rw [column_filter_card_eq_vertex_filter_card φ
      (fun z => D.connectedComponentMk z = c) y]
    rw [hvertexCol]
    have h := orderSixtyFour_eight_mul_componentNeighborFinset_card
      G hfree hmin hcover c y.1
    have : 8 * (componentNeighborFinset G D c y.1).card = 16 := by
      simpa [D, hc16] using h
    omega
  let K := {k : D.ConnectedComponent // k ≠ c}
  let σK : K → (e.supp ≃ f.supp) := fun k =>
    Classical.choose (exists_equiv_of_one_regular_grid φ
      (fun z => D.connectedComponentMk z = k.1)
      (hsmallRow k.1 k.2) (hsmallCol k.1 k.2))
  have hσK (k : K) (x : e.supp) :
      D.connectedComponentMk (φ.symm (x, σK k x)) = k.1 := by
    exact Classical.choose_spec (exists_equiv_of_one_regular_grid φ
      (fun z => D.connectedComponentMk z = k.1)
      (hsmallRow k.1 k.2) (hsmallCol k.1 k.2)) x
  have hKcard : Fintype.card K = 6 := by
    rw [Fintype.card_subtype_compl (fun k : D.ConnectedComponent => k = c), hcount]
    simp
  let κ : Fin 6 ≃ K :=
    (finCongr hKcard.symm).trans (Fintype.equivFin K).symm
  let σ : Fin 6 → (e.supp ≃ f.supp) := fun i => σK (κ i)
  obtain ⟨τ₀, τ₁, hτ₀, hτ₁, hτdisj⟩ :=
    exists_two_disjoint_equiv_of_two_regular_grid φ
      (fun z => D.connectedComponentMk z = c) hHRow hHCol
  refine ⟨φ, κ, σ, τ₀, τ₁, ?_, ?_, hτ₀, hτ₁, hτdisj, ?_⟩
  · intro i x
    exact hσK (κ i) x
  · intro i j hij x hEq
    have hcomp : (κ i).1 = (κ j).1 := by
      rw [← hσK (κ i) x, ← hσK (κ j) x, hEq]
    exact hij (κ.injective (Subtype.ext hcomp))
  · intro i x
    constructor
    · intro hEq
      have : (κ i).1 = c := by
        rw [← hσK (κ i) x, ← hτ₀ x, hEq]
      exact (κ i).2 this
    · intro hEq
      have : (κ i).1 = c := by
        rw [← hσK (κ i) x, ← hτ₁ x, hEq]
      exact (κ i).2 this

end

end Erdos85
