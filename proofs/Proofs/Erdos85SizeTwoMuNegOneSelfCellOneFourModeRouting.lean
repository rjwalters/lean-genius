import Proofs.Erdos85SizeTwoMuNegOneSelfCellOneFourStructure

/-!
# Shore-mode routing for the `mu=-1`, `(k,r)=(1,4)` terminal

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The checked owner terminal has three canonical diagonal cases: both shores
use offset three, exactly one shore uses offset one, or both shores use
offset one.  This file exposes those cases as named predicates and converts
the complete exterior-geometry socket into precisely that trichotomy while
retaining the signed cross-block data.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The offset-three (`triangle-free-owner`) shore model. -/
def MuNegOneOneFourTfShoreMode
    {X : Type*} (R : SimpleGraph X) (u : ZMod 8 → X) : Prop :=
  ∀ i j, R.Adj (u i) (u j) ↔ j - i = 3 ∨ j - i = 5

/-- The offset-one (`triangle-owner`) shore model. -/
def MuNegOneOneFourTriangleShoreMode
    {X : Type*} (R : SimpleGraph X) (u : ZMod 8 → X) : Prop :=
  ∀ i j, R.Adj (u i) (u j) ↔ j - i = 1 ∨ j - i = 7

/-- The three canonical unordered shore-mode families used by the owner
certificates.  The middle family remembers either orientation explicitly. -/
def MuNegOneOneFourCanonicalShoreModes
    {X : Type*} (R : SimpleGraph X) (u v : ZMod 8 → X) : Prop :=
  (MuNegOneOneFourTfShoreMode R u ∧ MuNegOneOneFourTfShoreMode R v) ∨
  ((MuNegOneOneFourTfShoreMode R u ∧
      MuNegOneOneFourTriangleShoreMode R v) ∨
    (MuNegOneOneFourTriangleShoreMode R u ∧
      MuNegOneOneFourTfShoreMode R v)) ∨
  (MuNegOneOneFourTriangleShoreMode R u ∧
    MuNegOneOneFourTriangleShoreMode R v)

theorem muNegOneOneFour_shoreExteriorModel_iff_modes
    {X : Type*} (R : SimpleGraph X) (u : ZMod 8 → X) :
    MuNegOneOneFourShoreExteriorModel R u ↔
      MuNegOneOneFourTfShoreMode R u ∨
        MuNegOneOneFourTriangleShoreMode R u := by
  rfl

/-- The four ordered mode pairs, useful when an encoding distinguishes the
two shores. -/
theorem muNegOneOneFour_ordered_shore_mode_cases
    {X : Type*} (R : SimpleGraph X) (u v : ZMod 8 → X)
    (hu : MuNegOneOneFourShoreExteriorModel R u)
    (hv : MuNegOneOneFourShoreExteriorModel R v) :
    (MuNegOneOneFourTfShoreMode R u ∧ MuNegOneOneFourTfShoreMode R v) ∨
    (MuNegOneOneFourTfShoreMode R u ∧ MuNegOneOneFourTriangleShoreMode R v) ∨
    (MuNegOneOneFourTriangleShoreMode R u ∧ MuNegOneOneFourTfShoreMode R v) ∨
    (MuNegOneOneFourTriangleShoreMode R u ∧
      MuNegOneOneFourTriangleShoreMode R v) := by
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact Or.inl ⟨hu, hv⟩
  · exact Or.inr (Or.inl ⟨hu, hv⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hu, hv⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hu, hv⟩))

/-- Swap-normalized three-way routing matching the three canonical owner
certificate families: TF/TF, mixed (in either order), and triangle/triangle. -/
theorem muNegOneOneFour_canonical_shore_mode_cases
    {X : Type*} (R : SimpleGraph X) (u v : ZMod 8 → X)
    (hu : MuNegOneOneFourShoreExteriorModel R u)
    (hv : MuNegOneOneFourShoreExteriorModel R v) :
    MuNegOneOneFourCanonicalShoreModes R u v := by
  rcases muNegOneOneFour_ordered_shore_mode_cases R u v hu hv with
      htt | htf | hft | hff
  · exact Or.inl htt
  · exact Or.inr (Or.inl (Or.inl htf))
  · exact Or.inr (Or.inl (Or.inr hft))
  · exact Or.inr (Or.inr hff)

/-- Terminal-facing adapter: retain the exact signed cross split while
collapsing the two independent shore disjunctions to the three canonical
certificate families. -/
theorem muNegOneOneFour_completeExteriorGeometry_modeRouting
    {X : Type*} (R : SimpleGraph X) [DecidableRel R.Adj]
    (u v : ZMod 8 → X) (su sv : ZMod 8 → ℤ)
    (hgeom : MuNegOneOneFourShoreExteriorModel R u ∧
      MuNegOneOneFourShoreExteriorModel R v ∧
      MuNegOneOneFourCrossExteriorSplit R u v su sv) :
    MuNegOneOneFourCrossExteriorSplit R u v su sv ∧
      MuNegOneOneFourCanonicalShoreModes R u v := by
  exact ⟨hgeom.2.2,
    muNegOneOneFour_canonical_shore_mode_cases R u v hgeom.1 hgeom.2.1⟩

/-- Graph-facing same-witness routing in the exact shape expected by the
three canonical owner-certificate consumers. -/
theorem orderSixtyFour_sizeTwo_muNegOne_refined_switch_or_oneFourOwnerModes
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
    let R := exteriorPairGraph G c.supp
    ∃ k r : ℕ, MuNegOneRefinedSectorCells N₁ N₂ k r ∧
      (sizeTwoMuSwitchTarget (-1) k r ≠ -1 ∨
        (MuNegOneOneFourCrossExteriorSplit R u v
            (fun i ↦ s (u i).1) (fun j ↦ s (v j).1) ∧
          MuNegOneOneFourCanonicalShoreModes R u v)) := by
  classical
  dsimp only
  obtain ⟨k, r, hcell, hswitch | hgeom⟩ :=
    orderSixtyFour_sizeTwo_muNegOne_refined_switch_or_completeExteriorGeometry
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
        u v huinj hvinj hurange hvrange hu hv
  · exact ⟨k, r, hcell, Or.inl hswitch⟩
  · exact ⟨k, r, hcell, Or.inr
      (muNegOneOneFour_completeExteriorGeometry_modeRouting _ _ _ _ _ hgeom)⟩

end

end Erdos85

#print axioms Erdos85.muNegOneOneFour_completeExteriorGeometry_modeRouting
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_refined_switch_or_oneFourOwnerModes
