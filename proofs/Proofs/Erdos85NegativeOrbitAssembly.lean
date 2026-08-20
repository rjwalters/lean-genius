import Proofs.Erdos85NegativeSwitchOrbit
import Proofs.Erdos85SizeTwoAlignedShoreSwitch
import Proofs.Erdos85EightEightCoordinateCover
import Proofs.Erdos85ComponentSignFlipEigenvector
import Proofs.Erdos85SizeTwoSwitchedJointExtension

/-!
# Ledger-backed assembly socket for the negative switch orbit

The arithmetic orbit eliminator must not erase the relation between its
parameters `(k,r)` and the signed graph witness.  This file packages the
common part of the three negative aligned ledgers and proves that its shore
flip produces an ambient witness at the *same* `(k,r)` and at exactly
`sizeTwoMuSwitchTarget theta k r`.

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The exact reduced cell predicate consumed by the negative orbit
eliminator.  Keeping the shore matrices in this predicate is essential:
the same arithmetic pair can be legal in one mode and illegal in another. -/
def NegativeEightEightOrbitCell
    (N₁ N₂ : Matrix (ZMod 8) (ZMod 8) ℤ)
    (theta : ℤ) (k r : ℕ) : Prop :=
  (theta = -5 ∧ MuNegFivePostMuOneSectorCells k r) ∨
  (theta = -3 ∧ MuNegThreePostMuOneSectorCells N₁ N₂ k r) ∨
  (theta = -1 ∧ MuNegOnePostEndpointSectorCells N₁ N₂ k r)

/-- Once the explicit `mu=-5` ledgers force both shore modes to be
all-one, every negative switch target is a valid refined target cell.  The
remaining `(1,4)` cell is exactly the positive exit. -/
theorem muNegFive_orbitCell_switch_of_allOne
    (N₁ N₂ : Matrix (ZMod 8) (ZMod 8) ℤ) (k r : ℕ)
    (hN₁ : C8CycleEntriesOne N₁) (hN₂ : C8CycleEntriesOne N₂)
    (hcell : MuNegFivePostMuOneSectorCells k r) :
    NegativeEightEightOrbitCell N₁ N₂
        (sizeTwoMuSwitchTarget (-5) k r) k r ∨
      sizeTwoMuSwitchTarget (-5) k r = 3 := by
  rcases hcell with h | h | h | h <;>
    rcases h with ⟨rfl, rfl⟩ <;>
    simp [NegativeEightEightOrbitCell, MuNegThreePostMuOneSectorCells,
      MuNegOnePostEndpointSectorCells, MuNegFivePostMuOneSectorCells,
      MuNegOneC8CycleEntriesOne, C8CycleEntriesOne,
      sizeTwoMuSwitchTarget] at hN₁ hN₂ ⊢ <;> aesop

/-- The reduced `mu=-3` mode table is closed under a negative shore switch;
its only nonnegative target is the checked `mu=3` exit. -/
theorem muNegThree_orbitCell_switch
    (N₁ N₂ : Matrix (ZMod 8) (ZMod 8) ℤ) (k r : ℕ)
    (hcell : MuNegThreePostMuOneSectorCells N₁ N₂ k r) :
    NegativeEightEightOrbitCell N₁ N₂
        (sizeTwoMuSwitchTarget (-3) k r) k r ∨
      sizeTwoMuSwitchTarget (-3) k r = 3 := by
  rcases hcell with hzero | hmixed | hone
  · rcases hzero.2.2 with h | h <;> rcases h with ⟨rfl, rfl⟩ <;>
      simp_all [NegativeEightEightOrbitCell,
        MuNegThreePostMuOneSectorCells, MuNegOnePostEndpointSectorCells,
        MuNegOneC8CycleEntriesZero, C8CycleEntriesZero,
        sizeTwoMuSwitchTarget]
  · rcases hmixed.2 with ⟨rfl, rfl⟩
    simp_all [NegativeEightEightOrbitCell,
      MuNegThreePostMuOneSectorCells, MuNegOnePostEndpointSectorCells,
      MuNegOneC8CycleEntriesZero, MuNegOneC8CycleEntriesOne,
      C8CycleEntriesZero, C8CycleEntriesOne, sizeTwoMuSwitchTarget]
  · rcases hone.2.2 with h | h | h | h <;>
      rcases h with ⟨rfl, rfl⟩ <;>
      simp_all [NegativeEightEightOrbitCell,
        MuNegFivePostMuOneSectorCells, MuNegThreePostMuOneSectorCells,
        MuNegOnePostEndpointSectorCells, MuNegOneC8CycleEntriesOne,
        C8CycleEntriesOne, sizeTwoMuSwitchTarget]

/-- The endpoint-reduced `mu=-1` mode table is likewise closed under every
negative target, with `(1,6)` as its sole positive exit. -/
theorem muNegOne_orbitCell_switch
    (N₁ N₂ : Matrix (ZMod 8) (ZMod 8) ℤ) (k r : ℕ)
    (hcell : MuNegOnePostEndpointSectorCells N₁ N₂ k r) :
    NegativeEightEightOrbitCell N₁ N₂
        (sizeTwoMuSwitchTarget (-1) k r) k r ∨
      sizeTwoMuSwitchTarget (-1) k r = 3 := by
  rcases hcell with hzero | hmixed | hone
  · rcases hzero.2 with h | h | h <;> rcases h with ⟨rfl, rfl⟩ <;>
      simp_all [NegativeEightEightOrbitCell,
        MuNegThreePostMuOneSectorCells, MuNegOnePostEndpointSectorCells,
        MuNegOneC8CycleEntriesZero, C8CycleEntriesZero,
        sizeTwoMuSwitchTarget]
  · rcases hmixed.2 with h | h <;> rcases h with ⟨rfl, rfl⟩ <;>
      simp_all [NegativeEightEightOrbitCell,
        MuNegThreePostMuOneSectorCells, MuNegOnePostEndpointSectorCells,
        MuNegOneC8CycleEntriesZero, MuNegOneC8CycleEntriesOne,
        C8CycleEntriesZero, C8CycleEntriesOne, sizeTwoMuSwitchTarget]
  · rcases hone.2 with h | h | h | h | h <;>
      rcases h with ⟨rfl, rfl⟩ <;>
      simp_all [NegativeEightEightOrbitCell,
        MuNegFivePostMuOneSectorCells, MuNegThreePostMuOneSectorCells,
        MuNegOnePostEndpointSectorCells, MuNegOneC8CycleEntriesOne,
        C8CycleEntriesOne, sizeTwoMuSwitchTarget]

/-- The graph-facing data shared by all three negative C8+C8 lanes.

Unlike `P theta k r := ∃ s, IsAmbientSignedJoint G c theta s`, the four
signed row counts and quotient identities below make `(k,r)` belong to the
same witness `s`.  `crossSame` is retained because its expression in terms
of `k` is lane-dependent; `hcoeff` records the common switch formula.
-/
structure NegativeEightEightAlignedWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (secondOrderDefectGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (a b : (G.induce c.supp).ConnectedComponent) (theta : ℤ) (k r : ℕ) where
  hab : a ≠ b
  cover : ∀ x : c.supp, x ∈ a.supp ∨ x ∈ b.supp
  s : V → ℤ
  signedJoint : IsAmbientSignedJoint G c theta s
  crossSame : ℕ
  quotientAA : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 7 - r
  quotientAB : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = r
  quotientBA : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b a = r
  quotientBB : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b b = 7 - r
  sameAA : ∀ x, x ∈ a.supp →
    ((componentNeighborFinset ((secondOrderDefectGraph G).induce c.supp)
      (G.induce c.supp) a x).filter
        (fun y ↦ s y.1 = s x.1)).card = k
  sameAB : ∀ x, x ∈ a.supp →
    ((componentNeighborFinset ((secondOrderDefectGraph G).induce c.supp)
      (G.induce c.supp) b x).filter
        (fun y ↦ s y.1 = s x.1)).card = crossSame
  sameBB : ∀ x, x ∈ b.supp →
    ((componentNeighborFinset ((secondOrderDefectGraph G).induce c.supp)
      (G.induce c.supp) b x).filter
        (fun y ↦ s y.1 = s x.1)).card = k
  sameBA : ∀ x, x ∈ b.supp →
    ((componentNeighborFinset ((secondOrderDefectGraph G).induce c.supp)
      (G.induce c.supp) a x).filter
        (fun y ↦ s y.1 = s x.1)).card = crossSame
  hcoeff : (2 * (k : ℤ) - (7 - r : ℕ)) -
      (2 * (crossSame : ℤ) - (r : ℤ)) = sizeTwoMuSwitchTarget theta k r

/-- The common aligned ledger is closed under the graph shore flip at the
level needed by the orbit eliminator: it creates a genuine ambient signed
joint witness at the exact arithmetic target while retaining `(k,r)`.

The finite lane-mode predicate is intentionally not hidden here.  Its
transport is a separate finite table lemma, so endpoint geometry cannot
silently detach from this witness.
-/
theorem NegativeEightEightAlignedWitness.exists_switched_ambient
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (secondOrderDefectGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (a b : (G.induce c.supp).ConnectedComponent) (theta : ℤ) (k r : ℕ)
    (hdegree : ∀ x : c.supp, (G.induce c.supp).degree x = 2)
    (hcomm : (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℝ) *
        ((G.induce c.supp).adjMatrix ℝ) =
      ((G.induce c.supp).adjMatrix ℝ) *
        (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℝ))
    (w : NegativeEightEightAlignedWitness G c a b theta k r) :
    ∃ t : V → ℤ,
      IsAmbientSignedJoint G c (sizeTwoMuSwitchTarget theta k r) t := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let B := (Finset.univ : Finset c.supp).filter
    (fun x ↦ H.connectedComponentMk x = b)
  let t : c.supp → ℤ := fun x ↦ if x ∈ B then -w.s x.1 else w.s x.1
  have hsign : ∀ x : c.supp, w.s x.1 = -1 ∨ w.s x.1 = 1 := by
    intro x
    exact w.signedJoint.2.1 x.1 x.2
  have htK : (K.adjMatrix ℤ).mulVec t =
      sizeTwoMuSwitchTarget theta k r • t := by
    have hraw := twoComponent_quotient_signSwitch_adjMatrix_eigen_sub_of_card
      K H a b w.hab hdegree hcomm w.cover (fun x ↦ w.s x.1)
        (7-r) k r w.crossSame hsign w.quotientAA w.quotientAB
          w.quotientBA w.quotientBB w.sameAA w.sameAB w.sameBB w.sameBA
    simpa only [t, B, w.hcoeff] using hraw
  have hsH : (H.adjMatrix ℤ).mulVec (fun x : c.supp ↦ w.s x.1) =
      (-2 : ℤ) • (fun x : c.supp ↦ w.s x.1) := by
    funext x
    rw [induce_adjMatrix_mulVec_restrict_apply]
    simpa [ConnectedComponent.mem_supp_iff, smul_eq_mul] using
      w.signedJoint.2.2.1 x.1 x.2
  have htH : (H.adjMatrix ℤ).mulVec t = (-2 : ℤ) • t := by
    simpa [t, B, Finset.mem_filter] using
      (connectedComponent_signFlip_adjMatrix_eigenvector
        H b (fun x : c.supp ↦ w.s x.1) (-2) hsH)
  have htsign : ∀ x, t x = -1 ∨ t x = 1 := by
    intro x
    have hx := hsign x
    by_cases hm : x ∈ B
    · simp only [t, hm, if_true]
      omega
    · simpa only [t, hm, if_false] using hx
  obtain ⟨T, hT⟩ := exists_isAmbientSignedJoint_of_induced
    G c t htsign (sizeTwoMuSwitchTarget theta k r)
      (by simpa [H] using htH) (by simpa [K] using htK)
  exact ⟨T, hT⟩

end

end Erdos85

#print axioms Erdos85.NegativeEightEightAlignedWitness.exists_switched_ambient
