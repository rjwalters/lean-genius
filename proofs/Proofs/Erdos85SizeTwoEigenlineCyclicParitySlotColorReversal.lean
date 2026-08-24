import Proofs.Erdos85SizeTwoEigenlineCyclicBinaryDefectParity
import Proofs.Erdos85SizeTwoEigenlineCyclicTargetFiberReciprocity

/-!
# Parity-slot colors under route reversal

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

The two endpoint slots of a routed dart have canonical colors in the PMR
partition.  Writing the target endpoint through the reversed dart makes the
global transport law exact: route reversal swaps the two endpoint colors.
This is the coordinate-free carrier for color-transition counts.
-/

namespace Erdos85

noncomputable section

/-- Canonical PMR color of the slot occupied by a dart at its source
endpoint.  The target-difference label is the source-difference label of the
reversed dart. -/
def SizeTwoCyclicRouteDart.sourceSlotColor
    {q : ℕ} [NeZero q] {a : ZMod q}
    {code : SizeTwoCyclicReciprocalPermutationCode q a}
    (h2q : 2 ∣ q) (e : SizeTwoCyclicRouteDart q a code) : ZMod q :=
  sizeTwoCyclicParitySlotColor h2q e.1.1 e.reverse.1.2.1.1

/-- Canonical PMR color of the slot occupied by a dart at its target
endpoint, expressed as the source slot of the reversed dart. -/
def SizeTwoCyclicRouteDart.targetSlotColor
    {q : ℕ} [NeZero q] {a : ZMod q}
    {code : SizeTwoCyclicReciprocalPermutationCode q a}
    (h2q : 2 ∣ q) (e : SizeTwoCyclicRouteDart q a code) : ZMod q :=
  sizeTwoCyclicParitySlotColor h2q e.reverse.1.1 e.1.2.1.1

/-- Reversing a route sends its source-slot color to its target-slot color. -/
theorem SizeTwoCyclicRouteDart.sourceSlotColor_reverse
    {q : ℕ} [NeZero q] {a : ZMod q}
    {code : SizeTwoCyclicReciprocalPermutationCode q a}
    (h2q : 2 ∣ q) (e : SizeTwoCyclicRouteDart q a code) :
    e.reverse.sourceSlotColor h2q = e.targetSlotColor h2q := by
  simp only [SizeTwoCyclicRouteDart.sourceSlotColor,
    SizeTwoCyclicRouteDart.targetSlotColor,
    SizeTwoCyclicRouteDart.reverse_reverse]

/-- Reversing a route sends its target-slot color to its source-slot color. -/
theorem SizeTwoCyclicRouteDart.targetSlotColor_reverse
    {q : ℕ} [NeZero q] {a : ZMod q}
    {code : SizeTwoCyclicReciprocalPermutationCode q a}
    (h2q : 2 ∣ q) (e : SizeTwoCyclicRouteDart q a code) :
    e.reverse.targetSlotColor h2q = e.sourceSlotColor h2q := by
  simp only [SizeTwoCyclicRouteDart.sourceSlotColor,
    SizeTwoCyclicRouteDart.targetSlotColor,
    SizeTwoCyclicRouteDart.reverse_reverse]

/-- The ordered endpoint-color pair is transposed by route reversal. -/
theorem SizeTwoCyclicRouteDart.slotColorPair_reverse
    {q : ℕ} [NeZero q] {a : ZMod q}
    {code : SizeTwoCyclicReciprocalPermutationCode q a}
    (h2q : 2 ∣ q) (e : SizeTwoCyclicRouteDart q a code) :
    (e.reverse.sourceSlotColor h2q, e.reverse.targetSlotColor h2q) =
      (e.targetSlotColor h2q, e.sourceSlotColor h2q) := by
  rw [e.sourceSlotColor_reverse h2q, e.targetSlotColor_reverse h2q]

/-- Routed darts with prescribed ordered endpoint colors. -/
def SizeTwoCyclicSlotColorTransition
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (h2q : 2 ∣ q) (x y : ZMod q) :=
  {e : SizeTwoCyclicRouteDart q a code //
    e.sourceSlotColor h2q = x ∧ e.targetSlotColor h2q = y}

noncomputable instance SizeTwoCyclicSlotColorTransition.instFintype
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (h2q : 2 ∣ q) (x y : ZMod q) :
    Fintype (SizeTwoCyclicSlotColorTransition code h2q x y) := by
  classical
  unfold SizeTwoCyclicSlotColorTransition
  infer_instance

/-- Route reversal transposes the two prescribed endpoint colors. -/
def sizeTwoCyclicSlotColorTransitionReverseEquiv
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (h2q : 2 ∣ q) (x y : ZMod q) :
    SizeTwoCyclicSlotColorTransition code h2q x y ≃
      SizeTwoCyclicSlotColorTransition code h2q y x where
  toFun e := ⟨e.1.reverse, by
    rw [e.1.sourceSlotColor_reverse h2q, e.1.targetSlotColor_reverse h2q]
    exact ⟨e.2.2, e.2.1⟩⟩
  invFun e := ⟨e.1.reverse, by
    rw [e.1.sourceSlotColor_reverse h2q, e.1.targetSlotColor_reverse h2q]
    exact ⟨e.2.2, e.2.1⟩⟩
  left_inv e := by
    apply Subtype.ext
    exact e.1.reverse_reverse
  right_inv e := by
    apply Subtype.ext
    exact e.1.reverse_reverse

/-- The base-resolved PMR color-transition matrix. -/
def sizeTwoCyclicSlotColorTransitionCount
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (h2q : 2 ∣ q) (x y : ZMod q) : ℕ :=
  Fintype.card (SizeTwoCyclicSlotColorTransition code h2q x y)

/-- The PMR color-transition matrix is symmetric. -/
theorem sizeTwoCyclicSlotColorTransitionCount_comm
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (h2q : 2 ∣ q) (x y : ZMod q) :
    sizeTwoCyclicSlotColorTransitionCount code h2q x y =
      sizeTwoCyclicSlotColorTransitionCount code h2q y x := by
  exact Fintype.card_congr
    (sizeTwoCyclicSlotColorTransitionReverseEquiv code h2q x y)

end

end Erdos85

#print axioms Erdos85.SizeTwoCyclicRouteDart.sourceSlotColor_reverse
#print axioms Erdos85.SizeTwoCyclicRouteDart.targetSlotColor_reverse
#print axioms Erdos85.SizeTwoCyclicRouteDart.slotColorPair_reverse
#print axioms Erdos85.sizeTwoCyclicSlotColorTransitionCount_comm
