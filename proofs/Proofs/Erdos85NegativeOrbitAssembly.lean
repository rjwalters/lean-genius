import Proofs.Erdos85NegativeSwitchOrbit
import Proofs.Erdos85SizeTwoAlignedShoreSwitch
import Proofs.Erdos85EightEightCoordinateCover
import Proofs.Erdos85ComponentSignFlipEigenvector
import Proofs.Erdos85SizeTwoSwitchedJointExtension
import Proofs.Erdos85MuNegFiveExplicitRowParameters
import Proofs.Erdos85AmbientMuThreeUnconditional
import Proofs.Erdos85SizeTwoSwitchedJointExclusions
import Proofs.Erdos85SizeTwoMuNegFiveAlignedShoreSwitch
import Proofs.Erdos85MuNegThreeOneTwoOrbitTerminal
import Proofs.Erdos85MuNegFiveZeroThreeGraphRealization
import Proofs.Erdos85MuNegOneOneFourEnrichedCapstone
import Proofs.Erdos85MuNegOneOneFourOwnerBridge
import Proofs.Erdos85SizeTwoMuNegThreeSelfCellZeroFourRouter
import Proofs.Erdos85MuNegThreeOneThreeCommutationTerminal
import Proofs.Erdos85MuNegSevenCompanionFreeKill

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

/-- Canonical ambient extension retaining its restriction to the source
component.  The older existential adapter intentionally hid this equality;
orbit endpoint coherence needs it. -/
theorem exists_isAmbientSignedJoint_of_induced_with_restrict
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (secondOrderDefectGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (t : c.supp → ℤ) (ht : ∀ x, t x = -1 ∨ t x = 1)
    (theta : ℤ)
    (hH : ((G.induce c.supp).adjMatrix ℤ).mulVec t = (-2 : ℤ) • t)
    (hD : (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ).mulVec t =
      theta • t) :
    ∃ s, IsAmbientSignedJoint G c theta s ∧
      ∀ x : c.supp, s x.1 = t x := by
  classical
  let D := secondOrderDefectGraph G
  let s := connectedComponentExtend D c t
  have hrestrict : ∀ x : c.supp, s x.1 = t x := by
    intro x
    simp [s, x.2]
  have hs_out : ∀ x, x ∉ c.supp → s x = 0 := by
    intro x hx
    simp [s, hx]
  have hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1 := by
    intro x hx
    simpa [s, hx] using ht ⟨x, hx⟩
  have hsH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ D.connectedComponentMk y = c), s y = -2 * s z := by
    intro z hz
    let zs : c.supp := ⟨z, hz⟩
    have hp := congrFun hH zs
    have hfun : (fun x : c.supp ↦ s x.1) = t := by
      funext x
      exact hrestrict x
    rw [← hfun] at hp
    rw [induce_adjMatrix_mulVec_restrict_apply G c.supp s zs] at hp
    simpa [D, s, hz, zs, ConnectedComponent.mem_supp_iff,
      smul_eq_mul] using hp
  have hsD : ∀ z ∈ c.supp, ∑ y ∈ D.neighborFinset z,
      s y = theta * s z := by
    intro z hz
    let zs : c.supp := ⟨z, hz⟩
    have hp := congrFun hD zs
    have hfun : (fun x : c.supp ↦ s x.1) = t := by
      funext x
      exact hrestrict x
    rw [← hfun] at hp
    change ((D.induce c.supp).adjMatrix ℤ).mulVec
      (fun x : c.supp ↦ s x.1) zs = _ at hp
    rw [induce_adjMatrix_mulVec_restrict_apply D c.supp s zs] at hp
    have hfilter : (D.neighborFinset z).filter (fun y ↦ y ∈ c.supp) =
        D.neighborFinset z := by
      apply Finset.filter_eq_self.mpr
      intro y hy
      exact c.mem_supp_of_adj_mem_supp hz ((D.mem_neighborFinset z y).mp hy)
    rw [hfilter] at hp
    simpa [s, hz, zs, smul_eq_mul] using hp
  exact ⟨s, ⟨hs_out, hs_in, by simpa [D] using hsH,
    by simpa [D] using hsD⟩, hrestrict⟩

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

theorem zmodEight_not_even_not_cycle_imp_middleOdd
    (d : ZMod 8) (heven : ¬ ZModEightEvenOffset d)
    (hone : d ≠ 1) (hnegOne : d ≠ -1) : d = 3 ∨ d = 5 := by
  revert d
  decide

theorem zmodEight_middleOdd_card_two :
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      j - 0 = 3 ∨ j - 0 = 5).card = 2 := by
  decide

/-- In each of the three `mu=-5` cells with a negative target, the every-row
ledger forces both distinguished cycle entries to occur.  If they were
absent, all opposite-sign internal neighbors of row zero would have to lie
at offsets 3 and 5, a set of size two; the ledger requires respectively
four, three, or four such neighbors. -/
theorem MuNegFiveExplicitRowParameterLedger.cycleEntriesOne_of_negativeCell
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ} {k r : ℕ}
    (L : MuNegFiveExplicitRowParameterLedger N M f g k r)
    (hmode : C8CycleEntriesZero N ∨ C8CycleEntriesOne N)
    (hcell : (k = 0 ∧ r = 3) ∨ (k = 0 ∧ r = 4) ∨
      (k = 1 ∧ r = 2)) : C8CycleEntriesOne N := by
  rcases hmode with hzero | hone
  · exfalso
    let D := (Finset.univ : Finset (ZMod 8)).filter fun j ↦ N 0 j = 1
    let O := D.filter fun j ↦ ¬ f j = f 0
    let T := (Finset.univ : Finset (ZMod 8)).filter fun j ↦
      j - 0 = 3 ∨ j - 0 = 5
    have hDcard : D.card = 7 - r := by simpa [D] using L.internal_row 0
    have hsame : (D.filter fun j ↦ f j = f 0).card = k := by
      rw [show D.filter (fun j ↦ f j = f 0) =
          (Finset.univ : Finset (ZMod 8)).filter
            (fun j ↦ f j = f 0 ∧ N 0 j = 1) by
        ext j
        simp [D, and_comm]]
      exact L.internal_same 0
    have hpart := Finset.card_filter_add_card_filter_not
      (fun j ↦ f j = f 0) (s := D)
    have hOcard : O.card = (7 - r) - k := by
      rw [hDcard, hsame] at hpart
      have hp : k + O.card = 7 - r := by simpa [O] using hpart
      omega
    have hsub : O ⊆ T := by
      intro j hj
      have hj' := Finset.mem_filter.mp hj
      have hedge : N 0 j = 1 := (Finset.mem_filter.mp hj'.1).2
      have hsignNe : ¬ f j = f 0 := hj'.2
      have hnotEven : ¬ ZModEightEvenOffset (j - 0) := by
        intro heven
        exact hsignNe ((zmodEight_alternating_sign_eq_iff_evenOffset
          f L.f_sign L.f_flip 0 j).2 heven)
      have hoffOne : j - 0 ≠ 1 := by
        intro hj1
        have : j = 1 := by simpa using hj1
        exact hzero.2 (this ▸ hedge)
      have hoffNegOne : j - 0 ≠ -1 := by
        intro hj1
        have : j = -1 := by simpa using hj1
        exact hzero.1 (this ▸ hedge)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        zmodEight_not_even_not_cycle_imp_middleOdd
          (j - 0) hnotEven hoffOne hoffNegOne⟩
    have hle : O.card ≤ 2 := by
      calc
        O.card ≤ T.card := Finset.card_le_card hsub
        _ = 2 := by simpa [T] using zmodEight_middleOdd_card_two
    rcases hcell with h | h | h <;> rcases h with ⟨rfl, rfl⟩ <;>
      norm_num at hOcard <;> omega
  · exact hone

/-- Fully coupled `mu=-5` mode transport.  This is the missing strengthening
of the arithmetic-only public post-cell predicate: both actual row ledgers
force precisely the modes required by the negative target table. -/
theorem muNegFive_orbitCell_switch_of_rowLedgers
    (N₁ M₁ N₂ M₂ : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f₁ f₂ : ZMod 8 → ℤ) (k r : ℕ)
    (L₁ : MuNegFiveExplicitRowParameterLedger N₁ M₁ f₁ f₂ k r)
    (L₂ : MuNegFiveExplicitRowParameterLedger N₂ M₂ f₂ f₁ k r)
    (hmode₁ : C8CycleEntriesZero N₁ ∨ C8CycleEntriesOne N₁)
    (hmode₂ : C8CycleEntriesZero N₂ ∨ C8CycleEntriesOne N₂)
    (hcell : MuNegFivePostMuOneSectorCells k r) :
    NegativeEightEightOrbitCell N₁ N₂
        (sizeTwoMuSwitchTarget (-5) k r) k r ∨
      sizeTwoMuSwitchTarget (-5) k r = 3 := by
  rcases hcell with h503 | h504 | h512 | h514
  · apply muNegFive_orbitCell_switch_of_allOne N₁ N₂ k r
      (L₁.cycleEntriesOne_of_negativeCell hmode₁ (Or.inl h503))
      (L₂.cycleEntriesOne_of_negativeCell hmode₂ (Or.inl h503))
      (Or.inl h503)
  · apply muNegFive_orbitCell_switch_of_allOne N₁ N₂ k r
      (L₁.cycleEntriesOne_of_negativeCell hmode₁ (Or.inr (Or.inl h504)))
      (L₂.cycleEntriesOne_of_negativeCell hmode₂ (Or.inr (Or.inl h504)))
      (Or.inr (Or.inl h504))
  · apply muNegFive_orbitCell_switch_of_allOne N₁ N₂ k r
      (L₁.cycleEntriesOne_of_negativeCell hmode₁ (Or.inr (Or.inr h512)))
      (L₂.cycleEntriesOne_of_negativeCell hmode₂ (Or.inr (Or.inr h512)))
      (Or.inr (Or.inr (Or.inl h512)))
  · exact Or.inr (by
      rcases h514 with ⟨rfl, rfl⟩
      norm_num [sizeTwoMuSwitchTarget])

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

/-- One-step form of the canonical orbit eliminator.

The original eliminator asks for a recursively closed predicate `P`, even
though its proof applies the shore switch at most once.  Graph witnesses are
naturally asymmetric: the source retains full aligned row ledgers, while the
transported endpoint only needs the switched ambient witness and its refined
cell.  Separate predicates `P` and `Q` express exactly that data flow without
requiring artificial reconstruction of unused source ledgers at the target.
-/
theorem negativeSwitchOrbits_false_of_canonical_endpoints_oneStep
    (P Q : ℤ → ℕ → ℕ → Prop)
    (N₁ N₂ : Matrix (ZMod 8) (ZMod 8) ℤ) (mu : ℤ) (k r : ℕ)
    (hP : P mu k r)
    (hcell : NegativeEightEightOrbitCell N₁ N₂ mu k r)
    (htransport : ∀ theta i j, P theta i j →
      Q (sizeTwoMuSwitchTarget theta i j) i j)
    (h503 : P (-5) 0 3 ∨ Q (-5) 0 3 → False)
    (h504 : P (-5) 0 4 ∨ Q (-5) 0 4 → False)
    (h512 : P (-5) 1 2 ∨ Q (-5) 1 2 → False)
    (h305 : P (-3) 0 5 ∨ Q (-3) 0 5 → False)
    (h313 : P (-3) 1 3 ∨ Q (-3) 1 3 → False)
    (h312 : P (-3) 1 2 ∨ Q (-3) 1 2 → False)
    (h114 : P (-1) 1 4 ∨ Q (-1) 1 4 → False)
    (hpos : ∀ i j, Q 3 i j → False) : False := by
  rcases hcell with ⟨rfl, h5⟩ | ⟨rfl, h3⟩ | ⟨rfl, h1⟩
  · rcases muNegFive_postMuOne_exact_switch_orbits k r h5 with
      h | h | h | h
    · rcases h with ⟨rfl, rfl, _⟩
      exact h503 (Or.inl hP)
    · rcases h with ⟨rfl, rfl, _⟩
      exact h504 (Or.inl hP)
    · rcases h with ⟨rfl, rfl, _⟩
      exact h512 (Or.inl hP)
    · rcases h with ⟨rfl, rfl, ht⟩
      exact hpos 1 4 (ht ▸ htransport (-5) 1 4 hP)
  · rcases muNegThree_postMuOne_exact_switch_orbits N₁ N₂ k r h3 with
      h | h | h | h | h
    · rcases h with ⟨rfl, rfl, ht⟩
      exact h503 (Or.inr (ht ▸ htransport (-3) 0 3 hP))
    · rcases h with ⟨rfl, rfl, _⟩
      exact h305 (Or.inl hP)
    · rcases h with ⟨rfl, rfl, _⟩
      exact h312 (Or.inl hP)
    · rcases h with ⟨rfl, rfl, _⟩
      exact h313 (Or.inl hP)
    · rcases h with ⟨rfl, rfl, ht⟩
      exact hpos 1 5 (ht ▸ htransport (-3) 1 5 hP)
  · rcases muNegOne_postEndpoint_exact_switch_orbits N₁ N₂ k r h1 with
      h | h | h | h | h | h
    · rcases h with ⟨rfl, rfl, ht⟩
      exact h504 (Or.inr (ht ▸ htransport (-1) 0 4 hP))
    · rcases h with ⟨rfl, rfl, ht⟩
      exact h305 (Or.inr (ht ▸ htransport (-1) 0 5 hP))
    · rcases h with ⟨rfl, rfl, ht⟩
      exact h512 (Or.inr (ht ▸ htransport (-1) 1 2 hP))
    · rcases h with ⟨rfl, rfl, ht⟩
      exact h313 (Or.inr (ht ▸ htransport (-1) 1 3 hP))
    · rcases h with ⟨rfl, rfl, _⟩
      exact h114 (Or.inl hP)
    · rcases h with ⟨rfl, rfl, ht⟩
      exact hpos 1 6 (ht ▸ htransport (-1) 1 6 hP)

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

/-- Translation between the support-filter presentation returned by the
three historical aligned-ledger theorems and the component-neighbor
presentation used by the common orbit witness. -/
theorem componentNeighbor_sameSign_eq_supportFilter
    {X : Type*} [Fintype X] [DecidableEq X]
    (D H : SimpleGraph X) [DecidableRel D.Adj] [DecidableRel H.Adj]
    [DecidableEq H.ConnectedComponent]
    (p : H.ConnectedComponent) (s : X → ℤ) (x : X) :
    (componentNeighborFinset D H p x).filter
        (fun y ↦ s y = s x) =
      ((Finset.univ : Finset X).filter (fun y ↦ y ∈ p.supp)).filter
        (fun y ↦ D.Adj x y ∧ s y = s x) := by
  ext y
  simp [componentNeighborFinset, SimpleGraph.mem_neighborFinset,
    and_left_comm, and_comm, and_assoc]

theorem componentQuotient_eq_of_coordinate_row
    {X : Type*} [Fintype X] [DecidableEq X]
    (D H : SimpleGraph X) [DecidableRel D.Adj] [DecidableRel H.Adj]
    [DecidableEq H.ConnectedComponent]
    (hdegree : ∀ x, H.degree x = 2)
    (hcomm : D.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * D.adjMatrix ℝ)
    (d p : H.ConnectedComponent) (A : Finset X)
    (u : ZMod 8 → X) (huinj : Function.Injective u)
    (hurange : Set.range u = ↑A) (hpRange : Set.range u = p.supp) (x : X)
    (hx : x ∈ d.supp) (q : ℕ)
    (hrow : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      D.Adj x (u j)).card = q) :
    componentQuotientMatrix D H d p = q := by
  rw [componentQuotientMatrix_apply_eq D H 2 hdegree hcomm d p hx]
  rw [coordinate_adj_card_eq_support_from D A u huinj hurange x] at hrow
  have heq : A.filter (fun y ↦ D.Adj x y) =
      componentNeighborFinset D H p x := by
    ext y
    have hmem : y ∈ A ↔ H.connectedComponentMk y = p := by
      rw [show y ∈ A ↔ y ∈ p.supp by
        change y ∈ (↑A : Set X) ↔ y ∈ p.supp
        rw [← hurange, ← hpRange]]
      exact ConnectedComponent.mem_supp_iff p y
    simp [componentNeighborFinset, SimpleGraph.mem_neighborFinset,
      hmem, and_comm]
  simpa [heq] using hrow

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

/-- Canonical switched ambient witness, retaining equality with the source
sign on the unflipped first shore. -/
theorem NegativeEightEightAlignedWitness.exists_switched_ambient_firstShore
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
    ∃ T : V → ℤ,
      IsAmbientSignedJoint G c (sizeTwoMuSwitchTarget theta k r) T ∧
      ∀ x : c.supp, x ∈ a.supp → T x.1 = w.s x.1 := by
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
  obtain ⟨T, hT, hrestrict⟩ :=
    exists_isAmbientSignedJoint_of_induced_with_restrict
      G c t htsign (sizeTwoMuSwitchTarget theta k r)
        (by simpa [H] using htH) (by simpa [K] using htK)
  refine ⟨T, hT, ?_⟩
  intro x hx
  rw [hrestrict]
  have hxa : H.connectedComponentMk x = a :=
    (ConnectedComponent.mem_supp_iff a x).mp hx
  have hxB : x ∉ B := by
    simp [B, hxa, w.hab]
  simp [t, hxB]

/-- Full source object for one orbit step.  Only the `mu=-5` source needs
extra mode data because its historical public cell predicate erased the
shore modes; the other two refined predicates already retain them. -/
structure NegativeEightEightSourceWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (secondOrderDefectGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (a b : (G.induce c.supp).ConnectedComponent)
    (N₁ N₂ : Matrix (ZMod 8) (ZMod 8) ℤ)
    (theta : ℤ) (k r : ℕ) where
  aligned : NegativeEightEightAlignedWitness G c a b theta k r
  cell : NegativeEightEightOrbitCell N₁ N₂ theta k r
  muNegFiveData : theta = -5 →
    ∃ (M₁ M₂ : Matrix (ZMod 8) (ZMod 8) ℤ) (f₁ f₂ : ZMod 8 → ℤ),
      MuNegFiveExplicitRowParameterLedger N₁ M₁ f₁ f₂ k r ∧
      MuNegFiveExplicitRowParameterLedger N₂ M₂ f₂ f₁ k r ∧
      (C8CycleEntriesZero N₁ ∨ C8CycleEntriesOne N₁) ∧
      (C8CycleEntriesZero N₂ ∨ C8CycleEntriesOne N₂)

/-- Target object after the single switch used by the canonical eliminator.
Negative targets retain their exact refined cell; the positive target is
recorded separately and is consumed by the unconditional `mu=3` terminal. -/
def NegativeEightEightTransportedWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (secondOrderDefectGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (a : (G.induce c.supp).ConnectedComponent)
    (N₁ N₂ : Matrix (ZMod 8) (ZMod 8) ℤ)
    (theta : ℤ) (k r : ℕ) : Prop :=
  ∃ s, IsAmbientSignedJoint G c theta s ∧
    componentQuotientMatrix ((secondOrderDefectGraph G).induce c.supp)
      (G.induce c.supp) a a = 7 - r ∧
    (∀ x, x ∈ a.supp →
      ((componentNeighborFinset ((secondOrderDefectGraph G).induce c.supp)
        (G.induce c.supp) a x).filter
          (fun y ↦ s y.1 = s x.1)).card = k) ∧
    (NegativeEightEightOrbitCell N₁ N₂ theta k r ∨ theta = 3)

/-- Ambient form of the size-two switched `mu=1` exclusion.  This is the
bridge needed by source constructors: the common aligned transport produces
an ambient witness, while the historical exclusion was stated for its
restriction to the component. -/
theorem isAmbientSignedJoint_theta_ne_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2) (theta : ℤ) (s : V → ℤ)
    (hs : IsAmbientSignedJoint G c theta s) : theta ≠ 1 := by
  intro htheta
  let t : c.supp → ℤ := fun x ↦ s x.1
  have htsign : ∀ x, t x = -1 ∨ t x = 1 := by
    intro x
    exact hs.2.1 x.1 x.2
  have htH : ((G.induce c.supp).adjMatrix ℤ).mulVec t =
      (-2 : ℤ) • t := by
    funext x
    rw [induce_adjMatrix_mulVec_restrict_apply]
    simpa [t, ConnectedComponent.mem_supp_iff, smul_eq_mul] using
      hs.2.2.1 x.1 x.2
  have htD : (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ).mulVec t =
      (1 : ℤ) • t := by
    funext x
    rw [induce_adjMatrix_mulVec_restrict_apply]
    have hrow := hs.2.2.2 x.1 x.2
    have hfilter : ((secondOrderDefectGraph G).neighborFinset x.1).filter
        (fun y ↦ y ∈ c.supp) =
        (secondOrderDefectGraph G).neighborFinset x.1 := by
      apply Finset.filter_eq_self.mpr
      intro y hy
      exact c.mem_supp_of_adj_mem_supp x.2
        (((secondOrderDefectGraph G).mem_neighborFinset x.1 y).mp hy)
    rw [hfilter]
    simpa [t, htheta, smul_eq_mul] using hrow
  exact orderSixtyFour_sizeTwoPart_inducedSignedJointEigenvector_muOne_false
    G hfree hreg hcard c hc t htsign htH htD

/-- Ambient form of the size-two negative-degree endpoint exclusion. -/
theorem isAmbientSignedJoint_theta_ne_negativeSeven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (theta : ℤ) (s : V → ℤ)
    (hs : IsAmbientSignedJoint G c theta s) : theta ≠ -7 := by
  intro htheta
  apply binarySquare_regular_allOpposite_defectEigenline_false
    G hfree (by omega) (by norm_num) hreg hcard c s hs.2.1
  intro z hz
  simpa [htheta] using hs.2.2.2 z hz

/-- Package a common aligned `mu=-3` ledger as a full orbit source.  The
post-`mu=1` refinement is derived from the switched ambient witness, so the
cell and `(k,r)` remain tied to the same source ledger. -/
theorem negativeEightEightSource_muNegThree_of_aligned
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
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent)
    (N₁ N₂ : Matrix (ZMod 8) (ZMod 8) ℤ) (k r : ℕ)
    (w : NegativeEightEightAlignedWitness G c a b (-3) k r)
    (hrefined : MuNegThreeRefinedSectorCells N₁ N₂ k r)
    (hdegree : ∀ x : c.supp, (G.induce c.supp).degree x = 2)
    (hcomm : (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℝ) *
        ((G.induce c.supp).adjMatrix ℝ) =
      ((G.induce c.supp).adjMatrix ℝ) *
        (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℝ)) :
    Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-3) k r) := by
  obtain ⟨t, ht⟩ := w.exists_switched_ambient G c a b (-3) k r hdegree hcomm
  have hne : sizeTwoMuSwitchTarget (-3) k r ≠ 1 :=
    isAmbientSignedJoint_theta_ne_one G hfree hreg hcard c hc _ t ht
  refine ⟨⟨w, Or.inr (Or.inl ⟨rfl,
    muNegThree_postMuOne_sector_cells_of_target_ne_one
      N₁ N₂ k r hrefined hne⟩), ?_⟩⟩
  intro h
  norm_num at h

/-- The analogous source packer for `mu=-5`.  Its two explicit row ledgers
and mode dichotomies are retained because they are exactly what the h5 finite
mode transport consumes. -/
theorem negativeEightEightSource_muNegFive_of_aligned
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
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent)
    (N₁ M₁ N₂ M₂ : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f₁ f₂ : ZMod 8 → ℤ) (k r : ℕ)
    (w : NegativeEightEightAlignedWitness G c a b (-5) k r)
    (hsector : MuNegFiveSectorCells k r)
    (L₁ : MuNegFiveExplicitRowParameterLedger N₁ M₁ f₁ f₂ k r)
    (L₂ : MuNegFiveExplicitRowParameterLedger N₂ M₂ f₂ f₁ k r)
    (hmode₁ : C8CycleEntriesZero N₁ ∨ C8CycleEntriesOne N₁)
    (hmode₂ : C8CycleEntriesZero N₂ ∨ C8CycleEntriesOne N₂)
    (hdegree : ∀ x : c.supp, (G.induce c.supp).degree x = 2)
    (hcomm : (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℝ) *
        ((G.induce c.supp).adjMatrix ℝ) =
      ((G.induce c.supp).adjMatrix ℝ) *
        (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℝ)) :
    Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-5) k r) := by
  obtain ⟨t, ht⟩ := w.exists_switched_ambient G c a b (-5) k r hdegree hcomm
  have hne : sizeTwoMuSwitchTarget (-5) k r ≠ 1 :=
    isAmbientSignedJoint_theta_ne_one G hfree hreg hcard c hc _ t ht
  have hpost := muNegFive_postMuOne_sector_cells_of_target_ne_one
    k r hsector hne
  refine ⟨⟨w, Or.inl ⟨rfl, hpost⟩, ?_⟩⟩
  intro _
  exact ⟨M₁, M₂, f₁, f₂, L₁, L₂, hmode₁, hmode₂⟩

/-- Package the endpoint-reduced `mu=-1` aligned ledger.  The negative-seven
exclusion is deliberately kept in the lane adapter, where its usual
other-component hypothesis is available. -/
theorem negativeEightEightSource_muNegOne_of_aligned
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (secondOrderDefectGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (a b : (G.induce c.supp).ConnectedComponent)
    (N₁ N₂ : Matrix (ZMod 8) (ZMod 8) ℤ) (k r : ℕ)
    (w : NegativeEightEightAlignedWitness G c a b (-1) k r)
    (hpost : MuNegOnePostEndpointSectorCells N₁ N₂ k r) :
    Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-1) k r) := by
  refine ⟨⟨w, Or.inr (Or.inr ⟨rfl, hpost⟩), ?_⟩⟩
  intro h
  norm_num at h

/-- Concrete adapter from the banked graph-facing `mu=-3` aligned-ledger
theorem into the global orbit source type. -/
theorem exists_negativeEightEightSource_muNegThree
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
    let K := (secondOrderDefectGraph G).induce c.supp
    let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (u j)
    let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (v j)
    ∃ k r, Nonempty
      (NegativeEightEightSourceWitness G c a b N₁ N₂ (-3) k r) := by
  classical
  dsimp only
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  let B := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ b.supp
  let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (v i) (v j)
  obtain ⟨k, r, hrefined, _ha8, _hb8, haa, habq, hbaq, hbb,
      hAA, hBB, hAB, hBA⟩ :=
    orderSixtyFour_sizeTwo_muNegThree_eightEight_refined_alignedLedger
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
        u v huinj hvinj hurange hvrange hu hv
  have hcover : ∀ x : c.supp, x ∈ a.supp ∨ x ∈ b.supp :=
    eightEight_shores_cover G c (by simpa using hc) a b hab
      u v huinj hvinj hurange hvrange
  have hdegree : ∀ x : c.supp, H.degree x = 2 := by
    intro x
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2) hc x
  have hcomm : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm G
      (secondOrderDefectGraph G) hglobal c).symm
  have hcoeff : (2 * (k : ℤ) - (7 - r : ℕ)) -
      (2 * (2 - k : ℕ) - (r : ℤ)) = sizeTwoMuSwitchTarget (-3) k r := by
    rcases hrefined with hzero | hmixed | hone
    · rcases hzero.2.2 with h | h | h | h <;>
        rcases h with ⟨rfl, rfl⟩ <;> norm_num [sizeTwoMuSwitchTarget]
    · rcases hmixed.2 with h | h <;>
        rcases h with ⟨rfl, rfl⟩ <;> norm_num [sizeTwoMuSwitchTarget]
    · rcases hone.2.2 with h | h | h | h | h <;>
        rcases h with ⟨rfl, rfl⟩ <;> norm_num [sizeTwoMuSwitchTarget]
  let w : NegativeEightEightAlignedWitness G c a b (-3) k r := {
    hab := hab
    cover := hcover
    s := s
    signedJoint := ⟨hs_out, hs_in, hH, hD⟩
    crossSame := 2 - k
    quotientAA := haa
    quotientAB := habq
    quotientBA := hbaq
    quotientBB := hbb
    sameAA := by
      intro x hx
      rw [componentNeighbor_sameSign_eq_supportFilter]
      exact hAA x (by simpa [A] using hx)
    sameAB := by
      intro x hx
      rw [componentNeighbor_sameSign_eq_supportFilter]
      exact hAB x (by simpa [A] using hx)
    sameBB := by
      intro x hx
      rw [componentNeighbor_sameSign_eq_supportFilter]
      exact hBB x (by simpa [B] using hx)
    sameBA := by
      intro x hx
      rw [componentNeighbor_sameSign_eq_supportFilter]
      exact hBA x (by simpa [B] using hx)
    hcoeff := hcoeff }
  refine ⟨k, r, negativeEightEightSource_muNegThree_of_aligned
    G hfree hreg hcard c hc a b N₁ N₂ k r w ?_ hdegree hcomm⟩
  exact hrefined

/-- Concrete adapter from the banked graph-facing `mu=-1` aligned ledger
into the global orbit source, including both switched endpoint exclusions. -/
theorem exists_negativeEightEightSource_muNegOne
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
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    let K := (secondOrderDefectGraph G).induce c.supp
    let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (u j)
    let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (v j)
    ∃ k r, Nonempty
      (NegativeEightEightSourceWitness G c a b N₁ N₂ (-1) k r) := by
  classical
  dsimp only
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  let B := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ b.supp
  let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (v i) (v j)
  obtain ⟨k, r, hrefined, _ha8, _hb8, haa, habq, hbaq, hbb,
      hAA, hBB, hAB, hBA⟩ :=
    orderSixtyFour_sizeTwo_muNegOne_eightEight_refined_alignedLedger
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
        u v huinj hvinj hurange hvrange hu hv
  have hcover : ∀ x : c.supp, x ∈ a.supp ∨ x ∈ b.supp :=
    eightEight_shores_cover G c (by simpa using hc) a b hab
      u v huinj hvinj hurange hvrange
  have hdegree : ∀ x : c.supp, H.degree x = 2 := by
    intro x
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2) hc x
  have hcomm : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm G
      (secondOrderDefectGraph G) hglobal c).symm
  have hcoeff : (2 * (k : ℤ) - (7 - r : ℕ)) -
      (2 * (3 - k : ℕ) - (r : ℤ)) = sizeTwoMuSwitchTarget (-1) k r := by
    rcases hrefined with hzero | hmixed | hone
    · rcases hzero.2 with h | h | h | h | h <;>
        rcases h with ⟨rfl, rfl⟩ <;> norm_num [sizeTwoMuSwitchTarget]
    · rcases hmixed.2 with h | h <;>
        rcases h with ⟨rfl, rfl⟩ <;> norm_num [sizeTwoMuSwitchTarget]
    · rcases hone.2 with h | h | h | h | h | h <;>
        rcases h with ⟨rfl, rfl⟩ <;> norm_num [sizeTwoMuSwitchTarget]
  let w : NegativeEightEightAlignedWitness G c a b (-1) k r := {
    hab := hab
    cover := hcover
    s := s
    signedJoint := ⟨hs_out, hs_in, hH, hD⟩
    crossSame := 3 - k
    quotientAA := haa
    quotientAB := habq
    quotientBA := hbaq
    quotientBB := hbb
    sameAA := by
      intro x hx
      rw [componentNeighbor_sameSign_eq_supportFilter]
      exact hAA x (by simpa [A] using hx)
    sameAB := by
      intro x hx
      rw [componentNeighbor_sameSign_eq_supportFilter]
      exact hAB x (by simpa [A] using hx)
    sameBB := by
      intro x hx
      rw [componentNeighbor_sameSign_eq_supportFilter]
      exact hBB x (by simpa [B] using hx)
    sameBA := by
      intro x hx
      rw [componentNeighbor_sameSign_eq_supportFilter]
      exact hBA x (by simpa [B] using hx)
    hcoeff := hcoeff }
  obtain ⟨t, ht⟩ := w.exists_switched_ambient G c a b (-1) k r hdegree hcomm
  have hneOne : sizeTwoMuSwitchTarget (-1) k r ≠ 1 :=
    isAmbientSignedJoint_theta_ne_one G hfree hreg hcard c hc _ t ht
  have hpostOne := muNegOne_postMuOne_sector_cells_of_target_ne_one
    N₁ N₂ k r hrefined hneOne
  have hneSeven : sizeTwoMuSwitchTarget (-1) k r ≠ -7 :=
    isAmbientSignedJoint_theta_ne_negativeSeven
      G hfree hreg hcard c hc _ t ht
  have hpost := muNegOne_postEndpoint_sector_cells_of_target_ne_negativeSeven
    N₁ N₂ k r hpostOne hneSeven
  exact ⟨k, r, negativeEightEightSource_muNegOne_of_aligned
    G c a b N₁ N₂ k r w hpost⟩

/-- Concrete adapter from the `mu=-5` graph-facing aligned shore-switch
package into the global orbit source.  The every-row ledgers reconstruct all
four quotient entries and all four signed component rows at the package's
own `(k,r)`, avoiding any existential-parameter mismatch. -/
theorem exists_negativeEightEightSource_muNegFive
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
    [DecidableRel (MuNegFiveNeutralProjection G c s)]
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hA_in : ∀ x ∈ c.supp, ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-5 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    let K := (secondOrderDefectGraph G).induce c.supp
    let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (u j)
    let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (v j)
    ∃ k r, Nonempty
      (NegativeEightEightSourceWitness G c a b N₁ N₂ (-5) k r) := by
  classical
  dsimp only
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  let B := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ b.supp
  let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  let M₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (v j)
  let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (v i) (v j)
  let M₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (v i) (u j)
  obtain ⟨k, r, hsector, hmode₁, hmode₂, _L₁, _L₂, LR₁, LR₂,
      _hK, _hHt, _htne, _htsign, _hneOne, _hpost, _htargets⟩ :=
    orderSixtyFour_sizeTwo_muNegFive_aligned_shoreSwitch
      G hfree hreg hcard c hc s hs_out hs_in hA_in hH hD a b hab
        u v huinj hvinj hurange hvrange hu hv
  have hurangeA : Set.range u = ↑A := by
    rw [hurange]
    ext x
    simp [A]
  have hvrangeB : Set.range v = ↑B := by
    rw [hvrange]
    ext x
    simp [B]
  have huA (i : ZMod 8) : u i ∈ a.supp := by
    rw [← hurange]
    exact ⟨i, rfl⟩
  have hvB (i : ZMod 8) : v i ∈ b.supp := by
    rw [← hvrange]
    exact ⟨i, rfl⟩
  have hcover : ∀ x : c.supp, x ∈ a.supp ∨ x ∈ b.supp :=
    eightEight_shores_cover G c (by simpa using hc) a b hab
      u v huinj hvinj hurange hvrange
  have hdegree : ∀ x : c.supp, H.degree x = 2 := by
    intro x
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2) hc x
  have hcomm : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm G
      (secondOrderDefectGraph G) hglobal c).symm
  have hN₁row (i : ZMod 8) :
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        K.Adj (u i) (u j)).card = 7 - r := by
    simpa [N₁, K, SimpleGraph.adjMatrix_apply] using LR₁.internal_row i
  have hM₁row (i : ZMod 8) :
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        K.Adj (u i) (v j)).card = r := by
    simpa [M₁, K, SimpleGraph.adjMatrix_apply] using LR₁.cross_row i
  have hN₂row (i : ZMod 8) :
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        K.Adj (v i) (v j)).card = 7 - r := by
    simpa [N₂, K, SimpleGraph.adjMatrix_apply] using LR₂.internal_row i
  have hM₂row (i : ZMod 8) :
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        K.Adj (v i) (u j)).card = r := by
    simpa [M₂, K, SimpleGraph.adjMatrix_apply] using LR₂.cross_row i
  have haa := componentQuotient_eq_of_coordinate_row
    K H hdegree hcomm a a A u huinj hurangeA hurange
      (u 0) (huA 0) (7-r) (hN₁row 0)
  have habq := componentQuotient_eq_of_coordinate_row
    K H hdegree hcomm a b B v hvinj hvrangeB hvrange
      (u 0) (huA 0) r (hM₁row 0)
  have hbaq := componentQuotient_eq_of_coordinate_row
    K H hdegree hcomm b a A u huinj hurangeA hurange
      (v 0) (hvB 0) r (hM₂row 0)
  have hbb := componentQuotient_eq_of_coordinate_row
    K H hdegree hcomm b b B v hvinj hvrangeB hvrange
      (v 0) (hvB 0) (7-r) (hN₂row 0)
  have hcoeff : (2 * (k : ℤ) - (7 - r : ℕ)) -
      (2 * (1 - k : ℕ) - (r : ℤ)) = sizeTwoMuSwitchTarget (-5) k r := by
    rcases hsector with h | h | h | h | h | h <;>
      rcases h with ⟨rfl, rfl⟩ <;> norm_num [sizeTwoMuSwitchTarget]
  let w : NegativeEightEightAlignedWitness G c a b (-5) k r := {
    hab := hab
    cover := hcover
    s := s
    signedJoint := ⟨hs_out, hs_in, hH, hD⟩
    crossSame := 1 - k
    quotientAA := haa
    quotientAB := habq
    quotientBA := hbaq
    quotientBB := hbb
    sameAA := by
      intro x hx
      rw [← hurange] at hx
      obtain ⟨i, rfl⟩ := hx
      rw [componentNeighbor_sameSign_eq_supportFilter]
      rw [← coordinate_sameSign_adj_card_eq_support_from
        K A u huinj hurangeA (fun x ↦ s x.1) (u i)]
      simpa [N₁, K, SimpleGraph.adjMatrix_apply, and_comm] using LR₁.internal_same i
    sameAB := by
      intro x hx
      rw [← hurange] at hx
      obtain ⟨i, rfl⟩ := hx
      rw [componentNeighbor_sameSign_eq_supportFilter]
      rw [← coordinate_sameSign_adj_card_eq_support_from
        K B v hvinj hvrangeB (fun x ↦ s x.1) (u i)]
      simpa [M₁, K, SimpleGraph.adjMatrix_apply, and_comm] using LR₁.cross_same i
    sameBB := by
      intro x hx
      rw [← hvrange] at hx
      obtain ⟨i, rfl⟩ := hx
      rw [componentNeighbor_sameSign_eq_supportFilter]
      rw [← coordinate_sameSign_adj_card_eq_support_from
        K B v hvinj hvrangeB (fun x ↦ s x.1) (v i)]
      simpa [N₂, K, SimpleGraph.adjMatrix_apply, and_comm] using LR₂.internal_same i
    sameBA := by
      intro x hx
      rw [← hvrange] at hx
      obtain ⟨i, rfl⟩ := hx
      rw [componentNeighbor_sameSign_eq_supportFilter]
      rw [← coordinate_sameSign_adj_card_eq_support_from
        K A u huinj hurangeA (fun x ↦ s x.1) (v i)]
      simpa [M₂, K, SimpleGraph.adjMatrix_apply, and_comm] using LR₂.cross_same i
    hcoeff := hcoeff }
  exact ⟨k, r, negativeEightEightSource_muNegFive_of_aligned
    G hfree hreg hcard c hc a b N₁ M₁ N₂ M₂
      (fun i ↦ s (u i).1) (fun i ↦ s (v i).1) k r w hsector
      LR₁ LR₂ hmode₁ hmode₂ hdegree hcomm⟩

/-- A full source witness transports to the exact one-step target object.
This combines the ledger-backed graph switch with all three finite mode
transport theorems. -/
theorem NegativeEightEightSourceWitness.transport
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (secondOrderDefectGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (a b : (G.induce c.supp).ConnectedComponent)
    (N₁ N₂ : Matrix (ZMod 8) (ZMod 8) ℤ)
    (theta : ℤ) (k r : ℕ)
    (hdegree : ∀ x : c.supp, (G.induce c.supp).degree x = 2)
    (hcomm : (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℝ) *
        ((G.induce c.supp).adjMatrix ℝ) =
      ((G.induce c.supp).adjMatrix ℝ) *
        (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℝ))
    (w : NegativeEightEightSourceWitness G c a b N₁ N₂ theta k r) :
    NegativeEightEightTransportedWitness G c a N₁ N₂
      (sizeTwoMuSwitchTarget theta k r) k r := by
  obtain ⟨T, hT, hfirst⟩ :=
    w.aligned.exists_switched_ambient_firstShore
      G c a b theta k r hdegree hcomm
  refine ⟨T, hT, w.aligned.quotientAA, ?_, ?_⟩
  · intro x hx
    have heq :
        ((componentNeighborFinset ((secondOrderDefectGraph G).induce c.supp)
          (G.induce c.supp) a x).filter
            (fun y ↦ T y.1 = T x.1)) =
        ((componentNeighborFinset ((secondOrderDefectGraph G).induce c.supp)
          (G.induce c.supp) a x).filter
            (fun y ↦ w.aligned.s y.1 = w.aligned.s x.1)) := by
      ext y
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hy, hsame⟩
        have hya : y ∈ a.supp :=
          (ConnectedComponent.mem_supp_iff a y).mpr
            (Finset.mem_filter.mp hy).2
        rw [hfirst y hya, hfirst x hx] at hsame
        exact ⟨hy, hsame⟩
      · rintro ⟨hy, hsame⟩
        have hya : y ∈ a.supp :=
          (ConnectedComponent.mem_supp_iff a y).mpr
            (Finset.mem_filter.mp hy).2
        rw [hfirst y hya, hfirst x hx]
        exact ⟨hy, hsame⟩
    rw [heq]
    exact w.aligned.sameAA x hx
  rcases w.cell with ⟨htheta, h5⟩ | ⟨htheta, h3⟩ | ⟨htheta, h1⟩
  · subst theta
    obtain ⟨M₁, M₂, f₁, f₂, L₁, L₂, hm₁, hm₂⟩ := w.muNegFiveData rfl
    exact muNegFive_orbitCell_switch_of_rowLedgers
      N₁ M₁ N₂ M₂ f₁ f₂ k r L₁ L₂ hm₁ hm₂ h5
  · subst theta
    exact muNegThree_orbitCell_switch N₁ N₂ k r h3
  · subst theta
    exact muNegOne_orbitCell_switch N₁ N₂ k r h1

/-- Conditional global assembly for an arbitrary negative C8+C8 source.
The positive endpoint is discharged internally; the arguments are exactly
the seven remaining canonical negative graph terminals. -/
theorem false_of_negativeEightEightSource_of_canonicalTerminals
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
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent)
    (N₁ N₂ : Matrix (ZMod 8) (ZMod 8) ℤ)
    (theta : ℤ) (k r : ℕ)
    (w : NegativeEightEightSourceWitness G c a b N₁ N₂ theta k r)
    (h503 : Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-5) 0 3) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-5) 0 3 → False)
    (h504 : Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-5) 0 4) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-5) 0 4 → False)
    (h512 : Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-5) 1 2) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-5) 1 2 → False)
    (h305 : Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-3) 0 5) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-3) 0 5 → False)
    (h313 : Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-3) 1 3) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-3) 1 3 → False)
    (h312 : Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-3) 1 2) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-3) 1 2 → False)
    (h114 : Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-1) 1 4) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-1) 1 4 → False) :
    False := by
  have hdegree : ∀ x : c.supp, (G.induce c.supp).degree x = 2 := by
    intro x
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2) hc x
  have hcomm :
      (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℝ) *
          ((G.induce c.supp).adjMatrix ℝ) =
        ((G.induce c.supp).adjMatrix ℝ) *
          (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℝ) := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm G
      (secondOrderDefectGraph G) hglobal c).symm
  apply negativeSwitchOrbits_false_of_canonical_endpoints_oneStep
    (fun theta k r ↦ Nonempty
      (NegativeEightEightSourceWitness G c a b N₁ N₂ theta k r))
    (NegativeEightEightTransportedWitness G c a N₁ N₂)
    N₁ N₂ theta k r ⟨w⟩ w.cell
    (fun theta i j hw ↦ by
      obtain ⟨hw⟩ := hw
      exact hw.transport G c a b N₁ N₂ theta i j hdegree hcomm)
    h503 h504 h512 h305 h313 h312 h114
  intro i j hpos
  obtain ⟨s, hs, _haa, _hsame, _⟩ := hpos
  exact false_of_orderSixtyFour_sizeTwo_ambient_muThree
    G hfree hreg hcard c hc s hs

/-- Common first-shore view of a direct or once-transported endpoint. -/
theorem exists_firstShore_coherence_of_source_or_transported
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (secondOrderDefectGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (a b : (G.induce c.supp).ConnectedComponent)
    (N₁ N₂ : Matrix (ZMod 8) (ZMod 8) ℤ)
    (theta : ℤ) (k r : ℕ)
    (h : Nonempty (NegativeEightEightSourceWitness
          G c a b N₁ N₂ theta k r) ∨
        NegativeEightEightTransportedWitness G c a N₁ N₂ theta k r) :
    ∃ s, IsAmbientSignedJoint G c theta s ∧
      componentQuotientMatrix ((secondOrderDefectGraph G).induce c.supp)
        (G.induce c.supp) a a = 7 - r ∧
      ∀ x, x ∈ a.supp →
        ((componentNeighborFinset ((secondOrderDefectGraph G).induce c.supp)
          (G.induce c.supp) a x).filter
            (fun y ↦ s y.1 = s x.1)).card = k := by
  rcases h with ⟨⟨w⟩⟩ | h
  · exact ⟨w.aligned.s, w.aligned.signedJoint,
      w.aligned.quotientAA, w.aligned.sameAA⟩
  · obtain ⟨s, hs, haa, hsame, _⟩ := h
    exact ⟨s, hs, haa, hsame⟩

/-- The checked h312 graph terminal discharges both direct and transported
canonical endpoint objects once their first-shore coherence is retained. -/
theorem false_of_h312_source_or_transported
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
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    let K := (secondOrderDefectGraph G).induce c.supp
    let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (u j)
    let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (v j)
    Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-3) 1 2) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-3) 1 2 →
    False := by
  classical
  dsimp only
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (v i) (v j)
  intro h
  obtain ⟨s, hs, haa, hsame⟩ :=
    exists_firstShore_coherence_of_source_or_transported
      G c a b N₁ N₂ (-3) 1 2 h
  obtain ⟨k', r', hcell, hne, haa', L₁⟩ :=
    orderSixtyFour_sizeTwo_muNegThree_refined_switch_ne_self_of_oneTwo
      G hfree hreg hcard c hc s hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
        a b hab u v huinj hvinj hurange hvrange hu hv
  have hurangeA : Set.range u = ↑A := by
    rw [hurange]
    ext x
    simp [A]
  have huA : u 0 ∈ a.supp := by
    rw [← hurange]
    exact ⟨0, rfl⟩
  have hsame' :
      ((componentNeighborFinset K H a (u 0)).filter
        (fun y ↦ s y.1 = s (u 0).1)).card = k' := by
    rw [componentNeighbor_sameSign_eq_supportFilter]
    rw [← coordinate_sameSign_adj_card_eq_support_from
      K A u huinj hurangeA (fun x ↦ s x.1) (u 0)]
    simpa [N₁, K, SimpleGraph.adjMatrix_apply, and_comm] using
      L₁.internal_same 0
  have hk : k' = 1 := by
    have hs0 := hsame (u 0) huA
    have htmp : 1 = k' := by
      simpa [K, H] using hs0.symm.trans hsame'
    exact htmp.symm
  have hrle : r' ≤ 7 := by
    rcases hcell with hz | hm | ho
    · rcases hz.2.2 with h | h | h | h <;> omega
    · rcases hm.2 with h | h <;> omega
    · rcases ho.2.2 with h | h | h | h | h <;> omega
  have hr : r' = 2 := by
    norm_num at haa
    have heq : 7 - r' = 5 := haa'.symm.trans haa
    omega
  subst k'
  subst r'
  apply hne
  rw [hk]
  norm_num [sizeTwoMuSwitchTarget]

/-- Re-extract the full μ=-5 graph row ledgers at a supplied retained
first-shore parameter pair.  This is the common adapter kernel for h503,
h504, and h512. -/
theorem exists_muNegFive_exact_rowLedgers_of_firstShore
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
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (s : V → ℤ) (hs : IsAmbientSignedJoint G c (-5) s)
    (k r : ℕ) (hr : r ≤ 7)
    (haa : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a =
        7 - r)
    (hsame : ∀ x, x ∈ a.supp →
      ((componentNeighborFinset ((secondOrderDefectGraph G).induce c.supp)
        (G.induce c.supp) a x).filter
          (fun y ↦ s y.1 = s x.1)).card = k) :
    let K := (secondOrderDefectGraph G).induce c.supp
    let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (u j)
    let M₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (v j)
    let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (v j)
    let M₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (u j)
    MuNegFiveSectorCells k r ∧
      (C8CycleEntriesZero N₁ ∨ C8CycleEntriesOne N₁) ∧
      (C8CycleEntriesZero N₂ ∨ C8CycleEntriesOne N₂) ∧
      MuNegFiveExplicitRowParameterLedger N₁ M₁
        (fun i ↦ s (u i).1) (fun j ↦ s (v j).1) k r ∧
      MuNegFiveExplicitRowParameterLedger N₂ M₂
        (fun i ↦ s (v i).1) (fun j ↦ s (u j).1) k r := by
  classical
  dsimp only
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  have hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x := by
    intro x hx
    rw [← hs.2.2.1 x hx]
    symm
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hyc :
        (secondOrderDefectGraph G).connectedComponentMk y = c
    · simp [hyc]
    · have hyout : y ∉ c.supp := by
        intro hyin
        exact hyc ((ConnectedComponent.mem_supp_iff c y).mp hyin)
      simp [hyc, hs.1 y hyout]
  obtain ⟨k', r', hcell, hmode₁, hmode₂, _L₁, _L₂, LR₁, LR₂,
      _hK, _hHt, _htne, _htsign, _hneOne, _hpost, _htargets⟩ :=
    orderSixtyFour_sizeTwo_muNegFive_aligned_shoreSwitch
      G hfree hreg hcard c hc s hs.1 hs.2.1 hA_in hs.2.2.1 hs.2.2.2
        a b hab u v huinj hvinj hurange hvrange hu hv
  have hurangeA : Set.range u = ↑A := by
    rw [hurange]
    ext x
    simp [A]
  have huA : u 0 ∈ a.supp := by
    rw [← hurange]
    exact ⟨0, rfl⟩
  have hsame' :
      ((componentNeighborFinset K H a (u 0)).filter
        (fun y ↦ s y.1 = s (u 0).1)).card = k' := by
    rw [componentNeighbor_sameSign_eq_supportFilter]
    rw [← coordinate_sameSign_adj_card_eq_support_from
      K A u huinj hurangeA (fun x ↦ s x.1) (u 0)]
    simpa [N₁, K, SimpleGraph.adjMatrix_apply, and_comm] using
      LR₁.internal_same 0
  have hk : k' = k := by
    have hs0 := hsame (u 0) huA
    exact hsame'.symm.trans hs0
  have hdegree : ∀ x : c.supp, H.degree x = 2 := by
    intro x
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2) hc x
  have hcomm : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm G
      (secondOrderDefectGraph G) hglobal c).symm
  have haa' : componentQuotientMatrix K H a a = 7 - r' :=
    componentQuotient_eq_of_coordinate_row K H hdegree hcomm
      a a A u huinj hurangeA hurange (u 0) huA (7 - r') (by
        simpa [N₁, K, SimpleGraph.adjMatrix_apply] using LR₁.internal_row 0)
  have hr' : r' ≤ 7 := by
    rcases hcell with h | h | h | h | h | h <;>
      rcases h with ⟨rfl, rfl⟩ <;> omega
  have hreq : r' = r := by
    have heq : 7 - r' = 7 - r := haa'.symm.trans haa
    omega
  rw [hk, hreq] at hcell LR₁ LR₂
  exact ⟨hcell, hmode₁, hmode₂, LR₁, LR₂⟩

/-- Direct-or-transported wrapper around the exact μ=-5 row-ledger kernel.
This is the callback-ready input package for each canonical μ=-5 leaf. -/
theorem exists_muNegFive_exact_data_of_source_or_transported
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
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (k r : ℕ) (hr : r ≤ 7) :
    let K := (secondOrderDefectGraph G).induce c.supp
    let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (u j)
    let M₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (v j)
    let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (v j)
    let M₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (u j)
    (Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-5) k r) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-5) k r) →
    ∃ s, IsAmbientSignedJoint G c (-5) s ∧
      MuNegFiveSectorCells k r ∧
      (C8CycleEntriesZero N₁ ∨ C8CycleEntriesOne N₁) ∧
      (C8CycleEntriesZero N₂ ∨ C8CycleEntriesOne N₂) ∧
      MuNegFiveExplicitRowParameterLedger N₁ M₁
        (fun i ↦ s (u i).1) (fun j ↦ s (v j).1) k r ∧
      MuNegFiveExplicitRowParameterLedger N₂ M₂
        (fun i ↦ s (v i).1) (fun j ↦ s (u j).1) k r := by
  dsimp only
  intro h
  obtain ⟨s, hs, haa, hsame⟩ :=
    exists_firstShore_coherence_of_source_or_transported
      G c a b _ _ (-5) k r h
  exact ⟨s, hs,
    exists_muNegFive_exact_rowLedgers_of_firstShore
      G hfree hreg hcard c hc a b hab u v huinj hvinj hurange hvrange
        hu hv s hs k r hr haa hsame⟩

/-- Callback-ready exact data for any direct or transported μ=-3 endpoint.
The retained first-shore quotient and same-count identify the parameters of
the freshly reconstructed aligned ledgers. -/
theorem exists_muNegThree_exact_data_of_source_or_transported
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
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (k r : ℕ) (hr : r ≤ 7) :
    let K := (secondOrderDefectGraph G).induce c.supp
    let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (u j)
    let M₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (v j)
    let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (v j)
    let M₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (u j)
    (Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-3) k r) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-3) k r) →
    ∃ s, IsAmbientSignedJoint G c (-3) s ∧
      MuNegThreeRefinedSectorCells N₁ N₂ k r ∧
      MuNegThreeExplicitParameterLedger N₁ M₁
        (fun i ↦ s (u i).1) (fun j ↦ s (v j).1) k r ∧
      MuNegThreeExplicitParameterLedger N₂ M₂
        (fun i ↦ s (v i).1) (fun j ↦ s (u j).1) k r := by
  classical
  dsimp only
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (v i) (v j)
  intro h
  obtain ⟨s, hs, haa, hsame⟩ :=
    exists_firstShore_coherence_of_source_or_transported
      G c a b N₁ N₂ (-3) k r h
  obtain ⟨k', r', hcell, _hK, _hH, _htne, _htsign, _hneOne,
      _hpost, _htargets, _hglobal, _hT, _horient, haa', _hbb, L₁, L₂⟩ :=
    orderSixtyFour_sizeTwo_muNegThree_refined_shoreSwitch
      G hfree hreg hcard c hc s hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
        a b hab u v huinj hvinj hurange hvrange hu hv
  have hurangeA : Set.range u = ↑A := by
    rw [hurange]
    ext x
    simp [A]
  have huA : u 0 ∈ a.supp := by
    rw [← hurange]
    exact ⟨0, rfl⟩
  have hsame' :
      ((componentNeighborFinset K H a (u 0)).filter
        (fun y ↦ s y.1 = s (u 0).1)).card = k' := by
    rw [componentNeighbor_sameSign_eq_supportFilter]
    rw [← coordinate_sameSign_adj_card_eq_support_from
      K A u huinj hurangeA (fun x ↦ s x.1) (u 0)]
    simpa [N₁, K, SimpleGraph.adjMatrix_apply, and_comm] using
      L₁.internal_same 0
  have hk : k' = k :=
    hsame'.symm.trans (hsame (u 0) huA)
  have hr' : r' ≤ 7 := by
    rcases hcell with hz | hm | ho
    · rcases hz.2.2 with h | h | h | h <;> omega
    · rcases hm.2 with h | h <;> omega
    · rcases ho.2.2 with h | h | h | h | h <;> omega
  have hreq : r' = r := by
    have heq : 7 - r' = 7 - r := haa'.symm.trans haa
    omega
  rw [hk, hreq] at hcell L₁ L₂
  exact ⟨s, hs, hcell, L₁, L₂⟩

/-- The h504 endpoint is already excluded by the row-three opposite-sign
self-intertwiner obstruction.  Its historical graph socket was developed for
the μ=-3 self cell, but the socket itself only consumes the common ambient
signed-cycle ledger and is therefore valid verbatim at μ=-5. -/
theorem false_of_h504_source_or_transported
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
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    let K := (secondOrderDefectGraph G).induce c.supp
    let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (u j)
    let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (v j)
    Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-5) 0 4) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-5) 0 4 →
    False := by
  classical
  dsimp only
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (v i) (v j)
  intro h
  obtain ⟨s, hs, haa, hsame⟩ :=
    exists_firstShore_coherence_of_source_or_transported
      G c a b N₁ N₂ (-5) 0 4 h
  obtain ⟨_hcell, hmode₁, _hmode₂, LR₁, _LR₂⟩ :=
    exists_muNegFive_exact_rowLedgers_of_firstShore
      G hfree hreg hcard c hc a b hab u v huinj hvinj hurange hvrange
        hu hv s hs 0 4 (by omega) haa hsame
  have hone : C8CycleEntriesOne N₁ :=
    LR₁.cycleEntriesOne_of_negativeCell hmode₁
      (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have hsame0 : ∀ x ∈ (Finset.univ : Finset c.supp).filter
      (fun x ↦ x ∈ a.supp),
      (((Finset.univ : Finset c.supp).filter
        (fun x ↦ x ∈ a.supp)).filter fun y ↦
          K.Adj x y ∧ s y.1 = s x.1).card = 0 := by
    intro x hx
    have hxa : x ∈ a.supp := (Finset.mem_filter.mp hx).2
    rw [← componentNeighbor_sameSign_eq_supportFilter]
    simpa [K, H, and_comm] using hsame x hxa
  exact orderSixtyFour_sizeTwo_muNegThree_zeroFour_false_of_parameters
    G hfree hreg hcard c hc s hs.1 hs.2.1 hs.2.2.1 a u huinj hurange hu
      0 4 rfl rfl haa hsame0 (by simpa [N₁, K] using hone)

/-- Direct and transported h313 endpoints are excluded by subtracting their
forced antipodal matching and invoking the row-three self-intertwiner kill. -/
theorem false_of_h313_source_or_transported
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
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    let K := (secondOrderDefectGraph G).induce c.supp
    let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (u j)
    let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (v j)
    Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-3) 1 3) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-3) 1 3 →
    False := by
  classical
  dsimp only
  let K := (secondOrderDefectGraph G).induce c.supp
  let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  let M₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (v j)
  let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (v i) (v j)
  let M₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (v i) (u j)
  intro h
  obtain ⟨s, _hs, hcell, L₁, _L₂⟩ :=
    exists_muNegThree_exact_data_of_source_or_transported
      G hfree hreg hcard c hc a b hab u v huinj hvinj hurange hvrange
        hu hv 1 3 (by omega) h
  have hone := muNegThree_oneThree_bothCycleEntriesOne N₁ N₂ hcell
  exact muNegThreeOneThree_graph_false_of_rowLedger
    G hfree hreg hcard c hc a u huinj hurange hu M₁
      (fun i ↦ s (u i).1) (fun j ↦ s (v j).1) L₁ hone.1

/-- The checked h503 owner terminal discharges either a direct source or a
transported endpoint by re-extracting the full row ledgers from the retained
ambient witness and pinning their parameters with first-shore coherence. -/
theorem false_of_h503_source_or_transported
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
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    let K := (secondOrderDefectGraph G).induce c.supp
    let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (u j)
    let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (v j)
    Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-5) 0 3) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-5) 0 3 →
    False := by
  classical
  dsimp only
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (v i) (v j)
  intro h
  obtain ⟨s, hs, haa, hsame⟩ :=
    exists_firstShore_coherence_of_source_or_transported
      G c a b N₁ N₂ (-5) 0 3 h
  have hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x := by
    intro x hx
    rw [← hs.2.2.1 x hx]
    symm
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hyc :
        (secondOrderDefectGraph G).connectedComponentMk y = c
    · simp [hyc]
    · have hyout : y ∉ c.supp := by
        intro hyin
        exact hyc ((ConnectedComponent.mem_supp_iff c y).mp hyin)
      simp [hyc, hs.1 y hyout]
  obtain ⟨k', r', _hcell, _hmode₁, _hmode₂, _L₁, _L₂, LR₁, LR₂,
      _hK, _hHt, _htne, _htsign, _hneOne, _hpost, _htargets⟩ :=
    orderSixtyFour_sizeTwo_muNegFive_aligned_shoreSwitch
      G hfree hreg hcard c hc s hs.1 hs.2.1 hA_in hs.2.2.1 hs.2.2.2
        a b hab u v huinj hvinj hurange hvrange hu hv
  have hurangeA : Set.range u = ↑A := by
    rw [hurange]
    ext x
    simp [A]
  have huA : u 0 ∈ a.supp := by
    rw [← hurange]
    exact ⟨0, rfl⟩
  have hsame' :
      ((componentNeighborFinset K H a (u 0)).filter
        (fun y ↦ s y.1 = s (u 0).1)).card = k' := by
    rw [componentNeighbor_sameSign_eq_supportFilter]
    rw [← coordinate_sameSign_adj_card_eq_support_from
      K A u huinj hurangeA (fun x ↦ s x.1) (u 0)]
    simpa [N₁, K, SimpleGraph.adjMatrix_apply, and_comm] using
      LR₁.internal_same 0
  have hk : k' = 0 := by
    have hs0 := hsame (u 0) huA
    have htmp : 0 = k' := by
      simpa [K, H] using hs0.symm.trans hsame'
    exact htmp.symm
  have hdegree : ∀ x : c.supp, H.degree x = 2 := by
    intro x
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2) hc x
  have hcomm : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm G
      (secondOrderDefectGraph G) hglobal c).symm
  have haa' : componentQuotientMatrix K H a a = 7 - r' :=
    componentQuotient_eq_of_coordinate_row K H hdegree hcomm
      a a A u huinj hurangeA hurange (u 0) huA (7 - r') (by
        simpa [N₁, K, SimpleGraph.adjMatrix_apply] using LR₁.internal_row 0)
  have hr : r' = 3 := by
    norm_num at haa
    have heq : 7 - r' = 4 := haa'.symm.trans haa
    omega
  rw [hk, hr] at LR₁ LR₂
  let su : ZMod 8 → ℤ := fun i ↦ s (u i).1
  let sv : ZMod 8 → ℤ := fun j ↦ s (v j).1
  have hphase := zmodEight_two_alternating_sign_phase_routing
    su sv LR₁.f_sign LR₁.g_sign LR₁.f_flip LR₁.g_flip
  apply muNegFiveZeroThree_graph_false G c a b u v hfree hreg hcard hc
    hab huinj hvinj hurange hvrange hu hv s (muNegOneSigmaOf su sv)
  · intro x y hx hy
    have hp := muNegOneSigma_coherence su sv LR₁.f_sign LR₁.g_sign
      hphase x y hx hy
    have hb : muNegFiveZeroThreeSameSign (muNegOneSigmaOf su sv) x y =
        (muNegOneSign (muNegOneSigmaOf su sv) x ==
          muNegOneSign (muNegOneSigmaOf su sv) (8 + y)) := by
      generalize muNegOneSigmaOf su sv = sigma
      cases sigma <;> interval_cases x <;> interval_cases y <;>
        decide
    rw [hb]
    exact ⟨fun h ↦ (hp.mpr h).symm, fun h ↦ hp.mp h.symm⟩
  · simpa [su, sv, N₁, K] using LR₁
  · simpa [su, sv, N₂, K] using LR₂

/-- The checked ambient h114 terminal consumes exactly the coherence retained
by either the direct source or the transported endpoint. -/
theorem false_of_h114_source_or_transported
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
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    let K := (secondOrderDefectGraph G).induce c.supp
    let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (u j)
    let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (v j)
    Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-1) 1 4) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-1) 1 4 →
    False := by
  classical
  dsimp only
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (v i) (v j)
  intro h
  obtain ⟨s, hs, haa, hsame⟩ :=
    exists_firstShore_coherence_of_source_or_transported
      G c a b N₁ N₂ (-1) 1 4 h
  apply muNegOneOneFour_ambient_false_of_oneFour_ledger
    G hfree hreg hcard c hc a b hab u v huinj hvinj hurange hvrange
      hu hv s hs
  · norm_num at haa ⊢
    exact haa
  · refine ⟨u 0, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (ConnectedComponent.mem_supp_iff a (u 0)).mp (by
        rw [← hurange]
        exact ⟨0, rfl⟩)
    · rw [← componentNeighbor_sameSign_eq_supportFilter]
      exact hsame (u 0) (by
        rw [← hurange]
        exact ⟨0, rfl⟩)

/-- Global negative-orbit assembly with the checked h312 leaf discharged
internally.  Only the six genuinely open canonical callbacks remain. -/
theorem false_of_negativeEightEightSource_of_six_canonicalTerminals
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
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (theta : ℤ) (k r : ℕ) :
    let K := (secondOrderDefectGraph G).induce c.supp
    let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (u j)
    let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (v j)
    NegativeEightEightSourceWitness G c a b N₁ N₂ theta k r →
    (Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-5) 0 3) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-5) 0 3 → False) →
    (Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-5) 0 4) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-5) 0 4 → False) →
    (Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-5) 1 2) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-5) 1 2 → False) →
    (Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-3) 0 5) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-3) 0 5 → False) →
    (Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-3) 1 3) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-3) 1 3 → False) →
    (Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-1) 1 4) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-1) 1 4 → False) →
    False := by
  dsimp only
  intro w h503 h504 h512 h305 h313 h114
  exact false_of_negativeEightEightSource_of_canonicalTerminals
    G hfree hreg hcard c hc a b _ _ theta k r w
      h503 h504 h512 h305 h313
      (false_of_h312_source_or_transported G hfree hreg hcard c hc
        a b hab u v huinj hvinj hurange hvrange hu hv)
      h114

/-- Global negative-orbit assembly with both checked graph leaves h503 and
h312 discharged internally.  The residual callback frontier has size five. -/
theorem false_of_negativeEightEightSource_of_five_canonicalTerminals
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
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (theta : ℤ) (k r : ℕ) :
    let K := (secondOrderDefectGraph G).induce c.supp
    let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (u j)
    let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (v j)
    NegativeEightEightSourceWitness G c a b N₁ N₂ theta k r →
    (Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-5) 0 4) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-5) 0 4 → False) →
    (Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-5) 1 2) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-5) 1 2 → False) →
    (Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-3) 0 5) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-3) 0 5 → False) →
    (Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-3) 1 3) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-3) 1 3 → False) →
    (Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-1) 1 4) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-1) 1 4 → False) →
    False := by
  dsimp only
  intro w h504 h512 h305 h313 h114
  exact false_of_negativeEightEightSource_of_six_canonicalTerminals
    G hfree hreg hcard c hc a b hab u v huinj hvinj hurange hvrange hu hv
      theta k r w
      (false_of_h503_source_or_transported G hfree hreg hcard c hc
        a b hab u v huinj hvinj hurange hvrange hu hv)
      h504 h512 h305 h313 h114

/-- Global negative-orbit assembly with h503, h312, and h114 discharged
internally.  Four canonical callbacks remain. -/
theorem false_of_negativeEightEightSource_of_four_canonicalTerminals
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
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (theta : ℤ) (k r : ℕ) :
    let K := (secondOrderDefectGraph G).induce c.supp
    let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (u j)
    let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (v j)
    NegativeEightEightSourceWitness G c a b N₁ N₂ theta k r →
    (Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-5) 0 4) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-5) 0 4 → False) →
    (Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-5) 1 2) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-5) 1 2 → False) →
    (Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-3) 0 5) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-3) 0 5 → False) →
    (Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-3) 1 3) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-3) 1 3 → False) →
    False := by
  dsimp only
  intro w h504 h512 h305 h313
  exact false_of_negativeEightEightSource_of_five_canonicalTerminals
    G hfree hreg hcard c hc a b hab u v huinj hvinj hurange hvrange hu hv
      theta k r w h504 h512 h305 h313
      (false_of_h114_source_or_transported G hfree hreg hcard c hc
        a b hab u v huinj hvinj hurange hvrange hu hv)

/-- Global negative-orbit assembly with the algebraic h504 self-intertwiner
leaf discharged internally.  Only h512, h305, and h313 remain. -/
theorem false_of_negativeEightEightSource_of_three_canonicalTerminals
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
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (theta : ℤ) (k r : ℕ) :
    let K := (secondOrderDefectGraph G).induce c.supp
    let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (u j)
    let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (v j)
    NegativeEightEightSourceWitness G c a b N₁ N₂ theta k r →
    (Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-5) 1 2) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-5) 1 2 → False) →
    (Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-3) 0 5) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-3) 0 5 → False) →
    (Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-3) 1 3) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-3) 1 3 → False) →
    False := by
  dsimp only
  intro w h512 h305 h313
  exact false_of_negativeEightEightSource_of_four_canonicalTerminals
    G hfree hreg hcard c hc a b hab u v huinj hvinj hurange hvrange hu hv
      theta k r w
      (false_of_h504_source_or_transported G hfree hreg hcard c hc
        a b hab u v huinj hvinj hurange hvrange hu hv)
      h512 h305 h313

/-- Global negative-orbit assembly after the algebraic h313 antipode
subtraction kill.  Only h512 and h305 remain. -/
theorem false_of_negativeEightEightSource_of_two_canonicalTerminals
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
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (theta : ℤ) (k r : ℕ) :
    let K := (secondOrderDefectGraph G).induce c.supp
    let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (u j)
    let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (v j)
    NegativeEightEightSourceWitness G c a b N₁ N₂ theta k r →
    (Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-5) 1 2) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-5) 1 2 → False) →
    (Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-3) 0 5) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-3) 0 5 → False) →
    False := by
  dsimp only
  intro w h512 h305
  exact false_of_negativeEightEightSource_of_three_canonicalTerminals
    G hfree hreg hcard c hc a b hab u v huinj hvinj hurange hvrange hu hv
      theta k r w h512 h305
      (false_of_h313_source_or_transported G hfree hreg hcard c hc
        a b hab u v huinj hvinj hurange hvrange hu hv)

end

end Erdos85

#print axioms Erdos85.NegativeEightEightAlignedWitness.exists_switched_ambient
#print axioms Erdos85.MuNegFiveExplicitRowParameterLedger.cycleEntriesOne_of_negativeCell
#print axioms Erdos85.muNegFive_orbitCell_switch_of_rowLedgers
#print axioms Erdos85.negativeSwitchOrbits_false_of_canonical_endpoints_oneStep
#print axioms Erdos85.NegativeEightEightSourceWitness.transport
#print axioms Erdos85.false_of_negativeEightEightSource_of_canonicalTerminals
#print axioms Erdos85.isAmbientSignedJoint_theta_ne_one
#print axioms Erdos85.negativeEightEightSource_muNegThree_of_aligned
#print axioms Erdos85.negativeEightEightSource_muNegFive_of_aligned
#print axioms Erdos85.negativeEightEightSource_muNegOne_of_aligned
#print axioms Erdos85.exists_negativeEightEightSource_muNegThree
#print axioms Erdos85.isAmbientSignedJoint_theta_ne_negativeSeven
#print axioms Erdos85.exists_negativeEightEightSource_muNegOne
#print axioms Erdos85.componentQuotient_eq_of_coordinate_row
#print axioms Erdos85.exists_negativeEightEightSource_muNegFive
#print axioms Erdos85.exists_isAmbientSignedJoint_of_induced_with_restrict
#print axioms Erdos85.NegativeEightEightAlignedWitness.exists_switched_ambient_firstShore
#print axioms Erdos85.exists_firstShore_coherence_of_source_or_transported
#print axioms Erdos85.false_of_h312_source_or_transported
#print axioms Erdos85.exists_muNegFive_exact_rowLedgers_of_firstShore
#print axioms Erdos85.exists_muNegFive_exact_data_of_source_or_transported
#print axioms Erdos85.exists_muNegThree_exact_data_of_source_or_transported
#print axioms Erdos85.false_of_h504_source_or_transported
#print axioms Erdos85.false_of_h313_source_or_transported
#print axioms Erdos85.false_of_h503_source_or_transported
#print axioms Erdos85.false_of_h114_source_or_transported
#print axioms Erdos85.false_of_negativeEightEightSource_of_six_canonicalTerminals
#print axioms Erdos85.false_of_negativeEightEightSource_of_five_canonicalTerminals
#print axioms Erdos85.false_of_negativeEightEightSource_of_four_canonicalTerminals
#print axioms Erdos85.false_of_negativeEightEightSource_of_three_canonicalTerminals
#print axioms Erdos85.false_of_negativeEightEightSource_of_two_canonicalTerminals
