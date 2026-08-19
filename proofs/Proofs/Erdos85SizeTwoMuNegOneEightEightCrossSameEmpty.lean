import Proofs.Erdos85SizeTwoMuNegOneEightEightSignedParameterConsumer

/-! # The empty cross same-sign block in the `mu=-1`, `k=3` case -/

open Finset

namespace Erdos85

noncomputable section

/-- If one diagonal row has maximal same-sign degree three, then every
same-sign cross pair is a nonedge of the defect graph. -/
theorem orderSixtyFour_sizeTwo_muNegOne_eightEight_crossSame_empty_of_three
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
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-1 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (i₀ : ZMod 8)
    (hthree :
      (((Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp).filter
        (fun y ↦ (secondOrderDefectGraph G).Adj (u i₀).1 y.1 ∧
          s y.1 = s (u i₀).1)).card = 3) :
    ∀ i j, s (u i).1 = s (v j).1 →
      ¬ (secondOrderDefectGraph G).Adj (u i).1 (v j).1 := by
  classical
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  let B := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ b.supp
  obtain ⟨k, hk, hA, _hB, hcrossA, _hcrossB⟩ :=
    orderSixtyFour_sizeTwo_muNegOne_eightEight_signedParameter
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
  have huiA : u i₀ ∈ A := by
    have h : u i₀ ∈ a.supp := by
      rw [← hurange]
      exact ⟨i₀, rfl⟩
    simpa [A] using h
  have hk3 : k = 3 := by
    have hi := hA (u i₀) huiA
    have hthree' : (A.filter fun y ↦ K.Adj (u i₀) y ∧
        s y.1 = s (u i₀).1).card = 3 := by
      simpa [A, K] using hthree
    rw [hthree'] at hi
    omega
  intro i j hsign hadj
  have hui : u i ∈ A := by
    have h : u i ∈ a.supp := by
      rw [← hurange]
      exact ⟨i, rfl⟩
    simpa [A] using h
  have hvj : v j ∈ B := by
    have h : v j ∈ b.supp := by
      rw [← hvrange]
      exact ⟨j, rfl⟩
    simpa [B] using h
  have hcard0 := hcrossA (u i) hui
  rw [hk3] at hcard0
  have hmem : v j ∈ B.filter fun y ↦ K.Adj (u i) y ∧
      s y.1 = s (u i).1 := by
    rw [Finset.mem_filter]
    exact ⟨hvj, hadj, hsign.symm⟩
  have hpos := Finset.card_pos.mpr ⟨v j, hmem⟩
  rw [hcard0] at hpos
  omega

end


end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_eightEight_crossSame_empty_of_three
