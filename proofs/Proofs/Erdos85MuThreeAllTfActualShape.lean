import Proofs.Erdos85MuThreeAllTfCycleShapeClassification
import Proofs.Erdos85BinarySquareRegularParity
import Proofs.Erdos85ComponentLocalObstruction

/-! # Instantiating the all-TF shape classification on a size-two block -/

open SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Integer version of support restriction for an induced adjacency image. -/
theorem adjMatrix_mulVec_eq_induce_mulVec_of_support_int
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Set V) [Fintype S]
    (s : V → ℤ) (hs : ∀ y, y ∉ S → s y = 0) (x : S) :
    (G.adjMatrix ℤ).mulVec s x.1 =
      ((G.induce S).adjMatrix ℤ).mulVec (fun y : S => s y.1) x := by
  classical
  rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct]
  calc
    (∑ y : V, G.adjMatrix ℤ x.1 y * s y) =
        ∑ y : V, if y ∈ S then G.adjMatrix ℤ x.1 y * s y else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y ∈ S
      · simp [hy]
      · simp [hy, hs y hy]
    _ = ∑ y ∈ (Finset.univ : Finset V).filter (fun y => y ∈ S),
        G.adjMatrix ℤ x.1 y * s y := by rw [← Finset.sum_filter]
    _ = ∑ y : S, G.adjMatrix ℤ x.1 y.1 * s y.1 := by
      simpa using (Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset V)) (p := fun y => y ∈ S)
        (fun y => G.adjMatrix ℤ x.1 y * s y)).symm
    _ = ∑ y : S, (G.induce S).adjMatrix ℤ x y * s y.1 := by
      apply Finset.sum_congr rfl
      intro y _
      simp only [SimpleGraph.adjMatrix_apply]
      rfl

/-- The actual order-64 signed size-two internal graph has one of the three
certificate shapes. -/
theorem orderSixtyFour_signedSizeTwo_internal_mu3AllTfShape
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hA_in : ∀ x, x ∈ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 * s x) :
    ∃ (shape : Mu3AllTfShape) (rs : List Nat),
      (rs = match shape with
        | .c16 => [16]
        | .c10c6 => [10, 6]
        | .c8c8 => [8, 8]) ∧
      (↑rs : Multiset Nat) =
        (Finset.univ : Finset (G.induce c.supp).ConnectedComponent).val.map
          (fun a => a.supp.ncard) := by
  let H := G.induce c.supp
  let t : c.supp → ℤ := fun x => s x.1
  have hcardH : Fintype.card c.supp = 16 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hc]
  have hdegH : ∀ x, H.degree x = 2 := by
    intro x
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c hc x
  have hfreeH : ¬ containsC4 c.supp H := by
    rintro ⟨f, hf, hadj⟩
    apply hfree
    exact ⟨fun i => (f i).1, Subtype.val_injective.comp hf,
      fun i j hij => hadj i j hij⟩
  have hsignH : ∀ x, t x = -1 ∨ t x = 1 := by
    intro x
    exact hs_in x.1 x.2
  have hsumH : ∀ x, ∑ y ∈ H.neighborFinset x, t y = -2 * t x := by
    intro x
    rw [← SimpleGraph.adjMatrix_mulVec_apply]
    rw [← adjMatrix_mulVec_eq_induce_mulVec_of_support_int
      G c.supp s hs_out x]
    exact hA_in x.1 x.2
  exact exists_mu3AllTfShape_of_twoRegular_neighborSum
    H hcardH hdegH hfreeH t hsignH hsumH

end

end Erdos85
