import Proofs.Erdos85OrderFortyNineCanonicalTripleSystem

/-!
# Fiber census of the canonical order-49 profiles

The graph-facing census is proved structurally in
`Erdos85OrderFortyNineCanonicalTripleSystem`.  This file independently
checks that the generated canonical mask arrays have the same universal
description.  Only 18 representatives and 512 supports are involved.
-/

namespace Erdos85

open OrderFortyNineWitnessTable

set_option maxRecDepth 100000

/-- Number of canonical mask entries carrying exactly `S`. -/
def orderFortyNineMaskSupportFiberCount
    (masks : Array Nat) (S : Finset (Fin 9)) : Nat :=
  (Finset.univ.filter fun i : Fin 49 =>
    orderFortyNineMaskSupport masks i = S).card

theorem orderFortyNine_card_maskSupportFiber
    (masks : Array Nat) (S : Finset (Fin 9)) :
    Fintype.card {i : Fin 49 // orderFortyNineMaskSupport masks i = S} =
      orderFortyNineMaskSupportFiberCount masks S := by
  rw [Fintype.card_subtype]
  rfl

/-- The structural multiplicity prescribed by a canonical triple system:
highs and residual lows at the empty support; triple incidence at singletons;
one uncovered-pair block; one listed triple block; nothing larger. -/
def orderFortyNineCanonicalSupportMultiplicity
    (rep : OrderFortyNineH9System) (S : Finset (Fin 9)) : Nat :=
  let N := S.image Fin.val
  let triples := orderFortyNineRepresentativeTripleSet rep
  if S.card = 0 then
    13 - rep.length
  else if S.card = 1 then
    (triples.filter fun T => N ⊆ T).card
  else if S.card = 2 then
    if ∃ T ∈ triples, N ⊆ T then 0 else 1
  else if S.card = 3 then
    if N ∈ triples then 1 else 0
  else
    0

/-- Multiplicity after remembering whether a vertex belongs to the initial
nine high positions.  This separates the nine structural zero masks from the
residual low zero masks. -/
def orderFortyNineCanonicalVertexKeyMultiplicity
    (rep : OrderFortyNineH9System) (key : Bool × Finset (Fin 9)) : Nat :=
  if key.1 then
    if key.2.card = 0 then 9 else 0
  else if key.2.card = 0 then
    4 - rep.length
  else
    orderFortyNineCanonicalSupportMultiplicity rep key.2

def orderFortyNineMaskVertexKey (masks : Array Nat) (i : Fin 49) :
    Bool × Finset (Fin 9) :=
  (decide (i.val < 9), orderFortyNineMaskSupport masks i)

def orderFortyNineMaskVertexKeyFiberCount
    (masks : Array Nat) (key : Bool × Finset (Fin 9)) : Nat :=
  (Finset.univ.filter fun i : Fin 49 =>
    orderFortyNineMaskVertexKey masks i = key).card

theorem orderFortyNine_card_maskVertexKeyFiber
    (masks : Array Nat) (key : Bool × Finset (Fin 9)) :
    Fintype.card {i : Fin 49 // orderFortyNineMaskVertexKey masks i = key} =
      orderFortyNineMaskVertexKeyFiberCount masks key := by
  rw [Fintype.card_subtype]
  rfl

theorem orderFortyNineH9T2_profileFiberCount
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T2Systems) (S : Finset (Fin 9)) :
    orderFortyNineMaskSupportFiberCount
        (orderFortyNineH9ProfileMasks rep) S =
      orderFortyNineCanonicalSupportMultiplicity rep S := by
  native_decide +revert

theorem orderFortyNineH9T3_profileFiberCount
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T3Systems) (S : Finset (Fin 9)) :
    orderFortyNineMaskSupportFiberCount
        (orderFortyNineH9ProfileMasks rep) S =
      orderFortyNineCanonicalSupportMultiplicity rep S := by
  native_decide +revert

theorem orderFortyNineH9T4_profileFiberCount
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T4Systems) (S : Finset (Fin 9)) :
    orderFortyNineMaskSupportFiberCount
        (orderFortyNineH9ProfileMasks rep) S =
      orderFortyNineCanonicalSupportMultiplicity rep S := by
  native_decide +revert

theorem orderFortyNineH9T2_vertexKeyFiberCount
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T2Systems)
    (key : Bool × Finset (Fin 9)) :
    orderFortyNineMaskVertexKeyFiberCount
        (orderFortyNineH9ProfileMasks rep) key =
      orderFortyNineCanonicalVertexKeyMultiplicity rep key := by
  native_decide +revert

theorem orderFortyNineH9T3_vertexKeyFiberCount
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T3Systems)
    (key : Bool × Finset (Fin 9)) :
    orderFortyNineMaskVertexKeyFiberCount
        (orderFortyNineH9ProfileMasks rep) key =
      orderFortyNineCanonicalVertexKeyMultiplicity rep key := by
  native_decide +revert

theorem orderFortyNineH9T4_vertexKeyFiberCount
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T4Systems)
    (key : Bool × Finset (Fin 9)) :
    orderFortyNineMaskVertexKeyFiberCount
        (orderFortyNineH9ProfileMasks rep) key =
      orderFortyNineCanonicalVertexKeyMultiplicity rep key := by
  native_decide +revert

/-- A key that remembers the *identity* of each of the nine high vertices,
not merely membership in the high stratum.  This is the key needed by the
Boolean terminal, where bit `w` must refer to vertex `w`. -/
def orderFortyNineMaskAlignedVertexKey (masks : Array Nat) (i : Fin 49) :
    Option (Fin 9) × Finset (Fin 9) :=
  (if h : i.val < 9 then some ⟨i.val, h⟩ else none,
    orderFortyNineMaskSupport masks i)

def orderFortyNineCanonicalAlignedVertexKeyMultiplicity
    (rep : OrderFortyNineH9System)
    (key : Option (Fin 9) × Finset (Fin 9)) : Nat :=
  match key.1 with
  | some _ => if key.2.card = 0 then 1 else 0
  | none =>
      if key.2.card = 0 then 4 - rep.length
      else orderFortyNineCanonicalSupportMultiplicity rep key.2

def orderFortyNineMaskAlignedVertexKeyFiberCount
    (masks : Array Nat) (key : Option (Fin 9) × Finset (Fin 9)) : Nat :=
  (Finset.univ.filter fun i : Fin 49 =>
    orderFortyNineMaskAlignedVertexKey masks i = key).card

theorem orderFortyNine_card_maskAlignedVertexKeyFiber
    (masks : Array Nat) (key : Option (Fin 9) × Finset (Fin 9)) :
    Fintype.card {i : Fin 49 //
      orderFortyNineMaskAlignedVertexKey masks i = key} =
      orderFortyNineMaskAlignedVertexKeyFiberCount masks key := by
  rw [Fintype.card_subtype]
  rfl

theorem orderFortyNineH9T2_alignedVertexKeyFiberCount
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T2Systems)
    (key : Option (Fin 9) × Finset (Fin 9)) :
    orderFortyNineMaskAlignedVertexKeyFiberCount
        (orderFortyNineH9ProfileMasks rep) key =
      orderFortyNineCanonicalAlignedVertexKeyMultiplicity rep key := by
  native_decide +revert

theorem orderFortyNineH9T3_alignedVertexKeyFiberCount
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T3Systems)
    (key : Option (Fin 9) × Finset (Fin 9)) :
    orderFortyNineMaskAlignedVertexKeyFiberCount
        (orderFortyNineH9ProfileMasks rep) key =
      orderFortyNineCanonicalAlignedVertexKeyMultiplicity rep key := by
  native_decide +revert

theorem orderFortyNineH9T4_alignedVertexKeyFiberCount
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T4Systems)
    (key : Option (Fin 9) × Finset (Fin 9)) :
    orderFortyNineMaskAlignedVertexKeyFiberCount
        (orderFortyNineH9ProfileMasks rep) key =
      orderFortyNineCanonicalAlignedVertexKeyMultiplicity rep key := by
  native_decide +revert

theorem orderFortyNineH9T2_profileMasks_size
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T2Systems) :
    (orderFortyNineH9ProfileMasks rep).size = 49 := by
  native_decide +revert

theorem orderFortyNineH9T3_profileMasks_size
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T3Systems) :
    (orderFortyNineH9ProfileMasks rep).size = 49 := by
  native_decide +revert

theorem orderFortyNineH9T4_profileMasks_size
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T4Systems) :
    (orderFortyNineH9ProfileMasks rep).size = 49 := by
  native_decide +revert

end Erdos85
