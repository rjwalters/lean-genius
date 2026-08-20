import Proofs.Erdos85NegativeSignedJointConnectedCoordinates
import Proofs.Erdos85BinarySquareSizeTwoNegativeSupportProfiles
import Proofs.Erdos85NegativeSizeTwoThreeLevelAction

/-! # Exterior sign-pair census for a connected negative signed joint

Every exterior vertex owns exactly two vertices of the size-two component.
The signed sum on that pair is respectively `2`, `0`, or `-2`; these are the
positive-positive, mixed, and negative-negative owner fibres.  This file
records their exact cardinalities before any cyclic owner encoding is chosen.
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

def negativeSignedJointPositivePairOwners
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (s : V → ℤ) : Finset V :=
  Finset.univ.filter fun x ↦
    x ∉ c.supp ∧ (G.adjMatrix ℤ).mulVec s x = 2

def negativeSignedJointMixedPairOwners
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (s : V → ℤ) : Finset V :=
  Finset.univ.filter fun x ↦
    x ∉ c.supp ∧ (G.adjMatrix ℤ).mulVec s x = 0

def negativeSignedJointNegativePairOwners
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (s : V → ℤ) : Finset V :=
  Finset.univ.filter fun x ↦
    x ∉ c.supp ∧ (G.adjMatrix ℤ).mulVec s x = -2

/-- Exact `PP/PN/NN` exterior-owner census.  Connectedness is included in
the interface because this is the consumer-facing connected branch, although
the counting identity itself only needs the signed-joint equations. -/
theorem orderSixtyFour_negativeSignedJoint_connected_ownerProfile
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
    let PP := negativeSignedJointPositivePairOwners G c s
    let PN := negativeSignedJointMixedPairOwners G c s
    let NN := negativeSignedJointNegativePairOwners G c s
    (mu = -1 ∧ PP.card = 8 ∧ PN.card = 32 ∧ NN.card = 8) ∨
    (mu = -3 ∧ PP.card = 12 ∧ PN.card = 24 ∧ NN.card = 12) ∨
    (mu = -5 ∧ PP.card = 16 ∧ PN.card = 16 ∧ NN.card = 16) := by
  classical
  dsimp only
  let A := G.adjMatrix ℤ
  let w : Fin 64 → ℤ := fun x ↦ A.mulVec s x + 2 * s x
  let Sp := (Finset.univ : Finset (Fin 64)).filter fun x ↦ w x = 2
  let Sm := (Finset.univ : Finset (Fin 64)).filter fun x ↦ w x = -2
  let PP := negativeSignedJointPositivePairOwners G c s
  let PN := negativeSignedJointMixedPairOwners G c s
  let NN := negativeSignedJointNegativePairOwners G c s
  let O := (Finset.univ : Finset (Fin 64)).filter fun x ↦ x ∉ c.supp
  have P := orderSixtyFour_sizeTwo_signedJoint_derived
    G hfree hreg (by norm_num) c (by simpa using hc) s mu
      hs_out hs_in hH hD
  have hprofile := orderSixtyFour_sizeTwo_signedJoint_supportProfile_of_local
    G hfree hreg (by norm_num) c (by simpa using hc) s mu
      hs_out hs_in hH hD
  have hSpOut : Sp = PP := by
    ext x
    simp only [Sp, PP, negativeSignedJointPositivePairOwners,
      Finset.mem_filter, Finset.mem_univ, true_and]
    change A.mulVec s x + 2 * s x = 2 ↔ x ∉ c.supp ∧ A.mulVec s x = 2
    by_cases hx : x ∈ c.supp
    · rw [P.ambientAction_in x hx]
      rcases hs_in x hx with hs | hs <;> simp [hs, hx]
    · rw [hs_out x hx]
      simp [hx]
  have hSmOut : Sm = NN := by
    ext x
    simp only [Sm, NN, negativeSignedJointNegativePairOwners,
      Finset.mem_filter, Finset.mem_univ, true_and]
    change A.mulVec s x + 2 * s x = -2 ↔ x ∉ c.supp ∧ A.mulVec s x = -2
    by_cases hx : x ∈ c.supp
    · rw [P.ambientAction_in x hx]
      rcases hs_in x hx with hs | hs <;> simp [hs, hx]
    · rw [hs_out x hx]
      simp [hx]
  have hsizes := negative_sizeTwo_support_sizes mu Sp.card Sm.card
    hprofile.1 hprofile.2.1 hmu
  rw [hSpOut, hSmOut] at hsizes
  have hO : O = PP ∪ PN ∪ NN := by
    ext x
    simp only [O, PP, PN, NN, negativeSignedJointPositivePairOwners,
      negativeSignedJointMixedPairOwners, negativeSignedJointNegativePairOwners,
      Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hx
      rcases P.ambientAction_out x hx with hm | hz | hp
      · exact Or.inr ⟨hx, hm⟩
      · exact Or.inl (Or.inr ⟨hx, hz⟩)
      · exact Or.inl (Or.inl ⟨hx, hp⟩)
    · rintro ((hp | hz) | hn)
      · exact hp.1
      · exact hz.1
      · exact hn.1
  have hdisjPPPN : Disjoint PP PN := by
    rw [Finset.disjoint_left]
    intro x hp hn
    have hp' : x ∉ c.supp ∧ A.mulVec s x = 2 := by
      simpa only [PP, negativeSignedJointPositivePairOwners,
        Finset.mem_filter, Finset.mem_univ, true_and] using hp
    have hn' : x ∉ c.supp ∧ A.mulVec s x = 0 := by
      simpa only [PN, negativeSignedJointMixedPairOwners,
        Finset.mem_filter, Finset.mem_univ, true_and] using hn
    omega
  have hdisjPPNN : Disjoint PP NN := by
    rw [Finset.disjoint_left]
    intro x hp hn
    have hp' : x ∉ c.supp ∧ A.mulVec s x = 2 := by
      simpa only [PP, negativeSignedJointPositivePairOwners,
        Finset.mem_filter, Finset.mem_univ, true_and] using hp
    have hn' : x ∉ c.supp ∧ A.mulVec s x = -2 := by
      simpa only [NN, negativeSignedJointNegativePairOwners,
        Finset.mem_filter, Finset.mem_univ, true_and] using hn
    omega
  have hdisjPNNN : Disjoint PN NN := by
    rw [Finset.disjoint_left]
    intro x hp hn
    have hp' : x ∉ c.supp ∧ A.mulVec s x = 0 := by
      simpa only [PN, negativeSignedJointMixedPairOwners,
        Finset.mem_filter, Finset.mem_univ, true_and] using hp
    have hn' : x ∉ c.supp ∧ A.mulVec s x = -2 := by
      simpa only [NN, negativeSignedJointNegativePairOwners,
        Finset.mem_filter, Finset.mem_univ, true_and] using hn
    omega
  have hOCard : O.card = 48 := by
    have hCcard : ((Finset.univ : Finset (Fin 64)).filter
        fun x ↦ x ∈ c.supp).card = 16 := by
      let C := (Finset.univ : Finset (Fin 64)).filter fun x ↦ x ∈ c.supp
      have hset : (↑C : Set (Fin 64)) = c.supp := by ext x; simp [C]
      calc
        C.card = (↑C : Set (Fin 64)).ncard := by simp
        _ = c.supp.ncard := congrArg Set.ncard hset
        _ = 16 := hc
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Fin 64))) (p := fun x ↦ x ∈ c.supp)
    change _ + O.card = _ at hsplit
    rw [hCcard, Finset.card_univ] at hsplit
    norm_num at hsplit ⊢
    omega
  have hsum : PP.card + PN.card + NN.card = 48 := by
    have hu : (PP ∪ PN ∪ NN).card = PP.card + PN.card + NN.card := by
      rw [Finset.card_union_of_disjoint
        (Finset.disjoint_union_left.mpr ⟨hdisjPPNN, hdisjPNNN⟩),
        Finset.card_union_of_disjoint hdisjPPPN]
    rw [hO, hu] at hOCard
    exact hOCard
  rcases hsizes with h1 | h3 | h5
  · left
    have hpn : PN.card = 32 := by omega
    exact ⟨h1.1, h1.2.1, hpn, h1.2.2⟩
  · right; left
    have hpn : PN.card = 24 := by omega
    exact ⟨h3.1, h3.2.1, hpn, h3.2.2⟩
  · right; right
    have hpn : PN.card = 16 := by omega
    exact ⟨h5.1, h5.2.1, hpn, h5.2.2⟩

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_negativeSignedJoint_connected_ownerProfile
