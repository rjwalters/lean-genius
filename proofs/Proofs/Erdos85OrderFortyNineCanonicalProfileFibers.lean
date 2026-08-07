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

end Erdos85
