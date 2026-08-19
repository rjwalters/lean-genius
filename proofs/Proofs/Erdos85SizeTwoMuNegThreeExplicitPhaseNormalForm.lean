import Proofs.Erdos85ZModEightCyclicOrientationPhase

/-! # Explicit-phase μ=-3 C8+C8 normal form -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Graph-facing normal form with the `k=1` matching written directly as
one of the sixteen fixed orientation/phase relations used by the owner-grid
certificate family. -/
theorem orderSixtyFour_sizeTwo_muNegThree_eightEight_explicitPhase_normalForm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2) (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-3 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    ∃ k r : ℕ, k ≤ 1 ∧ 2 ≤ r ∧ r ≤ 7 ∧
      ((k = 0 ∧
        (∀ x ∈ (Finset.univ : Finset c.supp).filter (fun x ↦ x ∈ a.supp),
          (((Finset.univ : Finset c.supp).filter
              (fun x ↦ x ∈ b.supp)).filter
            (fun y ↦ ((secondOrderDefectGraph G).induce c.supp).Adj x y ∧
              s y.1 = s x.1)).card = 2) ∧
        (∀ x ∈ (Finset.univ : Finset c.supp).filter (fun x ↦ x ∈ b.supp),
          (((Finset.univ : Finset c.supp).filter
              (fun x ↦ x ∈ a.supp)).filter
            (fun y ↦ ((secondOrderDefectGraph G).induce c.supp).Adj x y ∧
              s y.1 = s x.1)).card = 2)) ∨
      (k = 1 ∧ ∃ t : ZMod 8,
        (∀ i j,
          (s (u i).1 = s (v j).1 ∧
            (secondOrderDefectGraph G).Adj (u i).1 (v j).1) ↔
              j = t + i) ∨
        (∀ i j,
          (s (u i).1 = s (v j).1 ∧
            (secondOrderDefectGraph G).Adj (u i).1 (v j).1) ↔
              j = t - i))) := by
  obtain ⟨k, r, hk, hr2, hr7, hform⟩ :=
    orderSixtyFour_sizeTwo_muNegThree_eightEight_signed_normalForm
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
        u v huinj hvinj hurange hvrange hu hv
  refine ⟨k, r, hk, hr2, hr7, ?_⟩
  rcases hform with hzero | hone
  · exact Or.inl hzero
  · right
    obtain ⟨hk1, φ, hrel, hrec⟩ := hone
    obtain ⟨t, hf | hr⟩ :=
      zmodEight_cyclic_orientation_exists_explicit_phase φ hrec
    · refine ⟨hk1, t, Or.inl ?_⟩
      intro i j
      rw [hrel i j, hf i]
    · refine ⟨hk1, t, Or.inr ?_⟩
      intro i j
      rw [hrel i j, hr i]

/-- An actual cross same-sign row of cardinality one selects the explicit
phase branch of the normal form, eliminating the `k=0` alternative. -/
theorem orderSixtyFour_sizeTwo_muNegThree_eightEight_crossSameOne_explicitPhase
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2) (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-3 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (hcrossOne :
      (((Finset.univ : Finset c.supp).filter
        (fun x ↦ x ∈ b.supp)).filter fun y ↦
          ((secondOrderDefectGraph G).induce c.supp).Adj (u 0) y ∧
            s y.1 = s (u 0).1).card = 1) :
    ∃ t : ZMod 8,
      (∀ i j,
        (s (u i).1 = s (v j).1 ∧
          (secondOrderDefectGraph G).Adj (u i).1 (v j).1) ↔
            j = t + i) ∨
      (∀ i j,
        (s (u i).1 = s (v j).1 ∧
          (secondOrderDefectGraph G).Adj (u i).1 (v j).1) ↔
            j = t - i) := by
  obtain ⟨k, r, _hk, _hr2, _hr7, hform⟩ :=
    orderSixtyFour_sizeTwo_muNegThree_eightEight_explicitPhase_normalForm
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
        u v huinj hvinj hurange hvrange hu hv
  rcases hform with hzero | hone
  · have hu0A : u 0 ∈ (Finset.univ : Finset c.supp).filter
        (fun x ↦ x ∈ a.supp) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [← hurange]
      exact ⟨0, rfl⟩
    have htwo := hzero.2.1 (u 0) hu0A
    have htwo' :
        (((Finset.univ : Finset c.supp).filter
          (fun x ↦ x ∈ b.supp)).filter fun y ↦
            ((secondOrderDefectGraph G).induce c.supp).Adj (u 0) y ∧
              s y.1 = s (u 0).1).card = 2 := by
      simpa using htwo
    rw [hcrossOne] at htwo'
    omega
  · exact hone.2

end


end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_eightEight_explicitPhase_normalForm
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_eightEight_crossSameOne_explicitPhase
