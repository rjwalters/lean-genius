import Proofs.Erdos85NegativeSwitchOrbit
import Proofs.Erdos85SizeTwoAlignedShoreSwitch
import Proofs.Erdos85EightEightCoordinateCover
import Proofs.Erdos85ComponentSignFlipEigenvector
import Proofs.Erdos85SizeTwoSwitchedJointExtension
import Proofs.Erdos85MuNegFiveExplicitRowParameters
import Proofs.Erdos85AmbientMuThreeUnconditional
import Proofs.Erdos85SizeTwoSwitchedJointExclusions

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
    (N₁ N₂ : Matrix (ZMod 8) (ZMod 8) ℤ)
    (theta : ℤ) (k r : ℕ) : Prop :=
  (∃ s, IsAmbientSignedJoint G c theta s) ∧
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
    NegativeEightEightTransportedWitness G c N₁ N₂
      (sizeTwoMuSwitchTarget theta k r) k r := by
  refine ⟨w.aligned.exists_switched_ambient G c a b theta k r
    hdegree hcomm, ?_⟩
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
      NegativeEightEightTransportedWitness G c N₁ N₂ (-5) 0 3 → False)
    (h504 : Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-5) 0 4) ∨
      NegativeEightEightTransportedWitness G c N₁ N₂ (-5) 0 4 → False)
    (h512 : Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-5) 1 2) ∨
      NegativeEightEightTransportedWitness G c N₁ N₂ (-5) 1 2 → False)
    (h305 : Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-3) 0 5) ∨
      NegativeEightEightTransportedWitness G c N₁ N₂ (-3) 0 5 → False)
    (h313 : Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-3) 1 3) ∨
      NegativeEightEightTransportedWitness G c N₁ N₂ (-3) 1 3 → False)
    (h312 : Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-3) 1 2) ∨
      NegativeEightEightTransportedWitness G c N₁ N₂ (-3) 1 2 → False)
    (h114 : Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-1) 1 4) ∨
      NegativeEightEightTransportedWitness G c N₁ N₂ (-1) 1 4 → False) :
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
    (NegativeEightEightTransportedWitness G c N₁ N₂)
    N₁ N₂ theta k r ⟨w⟩ w.cell
    (fun theta i j hw ↦ by
      obtain ⟨hw⟩ := hw
      exact hw.transport G c a b N₁ N₂ theta i j hdegree hcomm)
    h503 h504 h512 h305 h313 h312 h114
  intro i j hpos
  obtain ⟨⟨s, hs⟩, _⟩ := hpos
  exact false_of_orderSixtyFour_sizeTwo_ambient_muThree
    G hfree hreg hcard c hc s hs

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
