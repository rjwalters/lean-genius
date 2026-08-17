import Proofs.Erdos85BinarySquareRoutingRainbowEquiv

/-! # Symmetries of ordered owner-rainbow censuses -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Cyclically rotate an ordered owner rainbow and its three edge colors. -/
def ownerRainbowTriplesRotate
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (d e f c : (secondOrderDefectGraph G).ConnectedComponent) :
    ownerRainbowTriples G d e f c → ownerRainbowTriples G d f c e := fun t =>
  ⟨(t.1.2.1, (t.1.2.2, t.1.1)),
    t.2.2.1, t.2.2.2.1, t.2.1,
    t.2.2.2.2.2.1, t.2.2.2.2.2.2, t.2.2.2.2.1⟩

/-- Cyclic rotation is an equivalence (the inverse rotates twice). -/
def ownerRainbowTriplesRotateEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (d e f c : (secondOrderDefectGraph G).ConnectedComponent) :
    ownerRainbowTriples G d e f c ≃ ownerRainbowTriples G d f c e where
  toFun := ownerRainbowTriplesRotate G d e f c
  invFun := fun t => ownerRainbowTriplesRotate G d c e f
    (ownerRainbowTriplesRotate G d f c e t)
  left_inv := by
    rintro ⟨⟨y₁, y₂, y₃⟩, h12, h23, h31, hE, hF, hC⟩
    apply Subtype.ext
    simp [ownerRainbowTriplesRotate]
  right_inv := by
    rintro ⟨⟨y₁, y₂, y₃⟩, h12, h23, h31, hE, hF, hC⟩
    apply Subtype.ext
    simp [ownerRainbowTriplesRotate]

/-- Reverse an ordered owner rainbow.  The middle color stays fixed and the
first/third colors swap. -/
def ownerRainbowTriplesReverse
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (d e f c : (secondOrderDefectGraph G).ConnectedComponent) :
    ownerRainbowTriples G d e f c → ownerRainbowTriples G d c f e := fun t =>
  ⟨(t.1.1, (t.1.2.2, t.1.2.1)),
    t.2.2.2.1.symm, t.2.2.1.symm, t.2.1.symm,
    t.2.2.2.2.2.2.symm, t.2.2.2.2.2.1.symm, t.2.2.2.2.1.symm⟩

/-- Reversal is an involutive equivalence. -/
def ownerRainbowTriplesReverseEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (d e f c : (secondOrderDefectGraph G).ConnectedComponent) :
    ownerRainbowTriples G d e f c ≃ ownerRainbowTriples G d c f e where
  toFun := ownerRainbowTriplesReverse G d e f c
  invFun := ownerRainbowTriplesReverse G d c f e
  left_inv := by
    rintro ⟨⟨y₁, y₂, y₃⟩, h12, h23, h31, hE, hF, hC⟩
    apply Subtype.ext
    simp [ownerRainbowTriplesReverse]
  right_inv := by
    rintro ⟨⟨y₁, y₂, y₃⟩, h12, h23, h31, hE, hF, hC⟩
    apply Subtype.ext
    simp [ownerRainbowTriplesReverse]

/-- Cyclically permuting the three owner colors preserves the exact census. -/
theorem ownerRainbowTriples_card_eq_rotate
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (d e f c : (secondOrderDefectGraph G).ConnectedComponent) :
    Fintype.card (ownerRainbowTriples G d e f c) =
      Fintype.card (ownerRainbowTriples G d f c e) :=
  Fintype.card_congr (ownerRainbowTriplesRotateEquiv G d e f c)

/-- Reversing the orientation and swapping the first/third owner colors
preserves the exact census. -/
theorem ownerRainbowTriples_card_eq_reverse
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (d e f c : (secondOrderDefectGraph G).ConnectedComponent) :
    Fintype.card (ownerRainbowTriples G d e f c) =
      Fintype.card (ownerRainbowTriples G d c f e) :=
  Fintype.card_congr (ownerRainbowTriplesReverseEquiv G d e f c)

end

end Erdos85
