import Proofs.Erdos85BinarySquareSizeTwoSignedJointPackage
import Proofs.Erdos85ThreeLevelEigenSupportMinDegree

/-!
# Exact support profiles for the negative size-two joint eigenvalues

The signed joint-line package determines both the cardinalities and local
structure of the extreme fibres of `w = As + 2s`.  This is uniform in `mu`;
the three surviving negative values give fibre sizes `8`, `12`, and `16`.
-/

open SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Uniform local-interface support profile at order 64. -/
theorem orderSixtyFour_sizeTwo_signedJoint_supportProfile_of_local
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
    (s : V → ℤ) (mu : ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c), s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y = mu * s z) :
    let w := fun x => (G.adjMatrix ℤ).mulVec s x + 2 * s x
    let Sp := Finset.univ.filter fun x => w x = 2
    let Sm := Finset.univ.filter fun x => w x = -2
    Sp.card = Sm.card ∧
    4 * (Sp.card : ℤ) = 8 * (3 - mu) ∧
    (∀ u ∈ Sp, 2 ≤ ((G.neighborFinset u).filter fun y => y ∈ Sp).card) ∧
    (∀ u ∈ Sm, 2 ≤ ((G.neighborFinset u).filter fun y => y ∈ Sm).card) := by
  dsimp only
  let A := G.adjMatrix ℤ
  let w : V → ℤ := fun x => A.mulVec s x + 2 * s x
  let Sp := Finset.univ.filter fun x => w x = 2
  let Sm := Finset.univ.filter fun x => w x = -2
  have P := orderSixtyFour_sizeTwo_signedJoint_derived
    G hfree hreg hcard c hc s mu hs_out hs_in hH hD
  let SpOut := Finset.univ.filter fun x =>
    x ∉ c.supp ∧ A.mulVec s x = 2
  let SmOut := Finset.univ.filter fun x =>
    x ∉ c.supp ∧ A.mulVec s x = -2
  have hSp : Sp = SpOut := by
    ext x
    simp only [Sp, SpOut, Finset.mem_filter, Finset.mem_univ, true_and]
    change A.mulVec s x + 2 * s x = 2 ↔
      x ∉ c.supp ∧ A.mulVec s x = 2
    by_cases hx : x ∈ c.supp
    · have hA := P.ambientAction_in x hx
      rw [hA]
      constructor
      · intro h
        exfalso
        rcases hs_in x hx with hs | hs <;> rw [hs] at h <;> norm_num at h
      · intro h
        exact (h.1 hx).elim
    · rw [hs_out x hx]
      simp [hx]
  have hSm : Sm = SmOut := by
    ext x
    simp only [Sm, SmOut, Finset.mem_filter, Finset.mem_univ, true_and]
    change A.mulVec s x + 2 * s x = -2 ↔
      x ∉ c.supp ∧ A.mulVec s x = -2
    by_cases hx : x ∈ c.supp
    · have hA := P.ambientAction_in x hx
      rw [hA]
      constructor
      · intro h
        exfalso
        rcases hs_in x hx with hs | hs <;> rw [hs] at h <;> norm_num at h
      · intro h
        exact (h.1 hx).elim
    · rw [hs_out x hx]
      simp [hx]
  have hbalance := binarySquare_regular_signedEigenvector_outsideSupport_balance
    G hfree hreg c hc s mu hs_in hs_out P.sum_eq_zero P.defectAction
      P.ambientAction_in P.ambientAction_out
  change SpOut.card = SmOut.card ∧
    4 * (SpOut.card : ℤ) = 8 * (8 - 5 - mu) at hbalance
  have hmin := orderSixtyFour_sizeTwo_jointEigenvector_extremeSupport_minDegree
    G hfree hreg c s mu hs_out P.sum_eq_zero P.defectAction
      P.ambientAction_in P.ambientAction_out
  change (∀ u ∈ Sp, 2 ≤ ((G.neighborFinset u).filter fun y => y ∈ Sp).card) ∧
    (∀ u ∈ Sm, 2 ≤ ((G.neighborFinset u).filter fun y => y ∈ Sm).card) at hmin
  change Sp.card = Sm.card ∧
    4 * (Sp.card : ℤ) = 8 * (3 - mu) ∧
    (∀ u ∈ Sp, 2 ≤ ((G.neighborFinset u).filter fun y => y ∈ Sp).card) ∧
    (∀ u ∈ Sm, 2 ≤ ((G.neighborFinset u).filter fun y => y ∈ Sm).card)
  rw [hSp, hSm] at hmin ⊢
  exact ⟨hbalance.1, by simpa using hbalance.2, hmin.1, hmin.2⟩

/-- Arithmetic specialization of the uniform profile to the three surviving
negative values. -/
theorem negative_sizeTwo_support_sizes
    (mu : ℤ) (p n : ℕ) (hbal : p = n)
    (hmass : 4 * (p : ℤ) = 8 * (3 - mu))
    (hmu : mu = -1 ∨ mu = -3 ∨ mu = -5) :
    (mu = -1 ∧ p = 8 ∧ n = 8) ∨
    (mu = -3 ∧ p = 12 ∧ n = 12) ∨
    (mu = -5 ∧ p = 16 ∧ n = 16) := by
  rcases hmu with hmu | hmu | hmu <;> subst mu <;> omega

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_signedJoint_supportProfile_of_local
#print axioms Erdos85.negative_sizeTwo_support_sizes
