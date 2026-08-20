import Proofs.Erdos85NegativeSignedJointExteriorLocalCensus
import Proofs.Erdos85SignedLocalDegreeEigenvector

/-! # Exterior eigenvector supplied by a connected negative signed joint -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- The restricted sign vector of a connected negative signed joint is a
nonzero, zero-sum eigenvector of the exterior-pair graph.  Its eigenvalue is
uniformly `-mu-3`, hence `-2`, `0`, or `2` in the three negative sectors. -/
theorem orderSixtyFour_negativeSignedJoint_exteriorEigenvector
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 16)
    (hconn : (G.induce c.supp).Connected)
    (s : Fin 64 → ℤ) (mu : ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y = mu * s z)
    (hmu : mu = -1 ∨ mu = -3 ∨ mu = -5) :
    let R := exteriorPairGraph G c.supp
    let t : c.supp → ℤ := fun x ↦ s x.1
    t ≠ 0 ∧
      ∑ x, t x = 0 ∧
      (R.adjMatrix ℤ).mulVec t = (fun x ↦ (-mu - 3) * t x) ∧
      (mu = -1 → (R.adjMatrix ℤ).mulVec t = (fun x ↦ -2 * t x)) ∧
      (mu = -3 → (R.adjMatrix ℤ).mulVec t = 0) ∧
      (mu = -5 → (R.adjMatrix ℤ).mulVec t = (fun x ↦ 2 * t x)) := by
  classical
  let R := exteriorPairGraph G c.supp
  let t : c.supp → ℤ := fun x ↦ s x.1
  have hcard : Fintype.card (Fin 64) = 8 * 8 := by norm_num
  have P := orderSixtyFour_sizeTwo_signedJoint_derived
    G hfree hreg hcard c (by simpa using hc) s mu hs_out hs_in hH hD
  have htne : t ≠ 0 := by
    obtain ⟨x, hx⟩ := c.nonempty_supp
    intro ht
    have hz : s x = 0 := by
      simpa [t] using congrFun ht (⟨x, hx⟩ : c.supp)
    rcases hs_in x hx with hs | hs <;> omega
  have htsum : ∑ x, t x = 0 := by
    have hamb : ∑ x : Fin 64, s x = 0 := P.sum_eq_zero
    rw [← hamb]
    let Sc := Finset.univ.filter fun x : Fin 64 ↦ x ∈ c.supp
    calc
      (∑ x : c.supp, t x) = ∑ x ∈ Sc, s x := by
        apply Finset.sum_bij (fun x _ ↦ x.1)
        · intro x _
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩
        · intro x _ y _ hxy
          exact Subtype.ext hxy
        · intro x hx
          exact ⟨⟨x, (Finset.mem_filter.mp hx).2⟩, Finset.mem_univ _, rfl⟩
        · simp [t]
      _ = ∑ x, s x := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro x _ hx
        have hxout : x ∉ c.supp := by
          simpa [Sc] using hx
        simp [hs_out x hxout]
  have hsign : ∀ x : c.supp, t x = -1 ∨ t x = 1 := by
    intro x
    exact hs_in x.1 x.2
  have hlocal := orderSixtyFour_negativeSignedJoint_exteriorLocalCensus
    G hfree hreg c hc hconn s mu hs_out hs_in hH hD
  have heig (a b : ℕ)
      (hsame : ∀ x, ((R.neighborFinset x).filter fun y ↦ t y = t x).card = a)
      (hopp : ∀ x, ((R.neighborFinset x).filter fun y ↦ t y ≠ t x).card = b) :
      (R.adjMatrix ℤ).mulVec t = fun x ↦ ((a : ℤ) - b) * t x :=
    adjMatrix_mulVec_eq_same_sub_opposite R t a b hsign hsame hopp
  have hformula : (R.adjMatrix ℤ).mulVec t = fun x ↦ (-mu - 3) * t x := by
    rcases hmu with hm | hm | hm
    · have hl : ∀ x, ((R.neighborFinset x).filter fun y ↦ t y = t x).card = 2 ∧
          ((R.neighborFinset x).filter fun y ↦ t y ≠ t x).card = 4 := by
        intro x
        simpa [R, t] using (hlocal x).1 hm
      simpa [hm] using heig 2 4 (fun x ↦ (hl x).1) (fun x ↦ (hl x).2)
    · have hl : ∀ x, ((R.neighborFinset x).filter fun y ↦ t y = t x).card = 3 ∧
          ((R.neighborFinset x).filter fun y ↦ t y ≠ t x).card = 3 := by
        intro x
        simpa [R, t] using (hlocal x).2.1 hm
      simpa [hm] using heig 3 3 (fun x ↦ (hl x).1) (fun x ↦ (hl x).2)
    · have hl : ∀ x, ((R.neighborFinset x).filter fun y ↦ t y = t x).card = 4 ∧
          ((R.neighborFinset x).filter fun y ↦ t y ≠ t x).card = 2 := by
        intro x
        simpa [R, t] using (hlocal x).2.2 hm
      simpa [hm] using heig 4 2 (fun x ↦ (hl x).1) (fun x ↦ (hl x).2)
  refine ⟨htne, htsum, hformula, ?_, ?_, ?_⟩
  · intro hm
    simpa [hm] using hformula
  · intro hm
    change (R.adjMatrix ℤ).mulVec t = 0
    rw [hformula]
    funext x
    simp [hm]
  · intro hm
    simpa [hm] using hformula

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_negativeSignedJoint_exteriorEigenvector
