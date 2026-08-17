import Proofs.Erdos85RoutingOwnerRainbowExactColors

/-! # Two incident closed private-orbit blocks collide -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Consider two incident edges `ab, ac` of one near-twin triangle whose
private partners are the incident edges `de, df` of the other triangle.  If
each edge/partner pair closes into one `K₂,₂` in its fork owner factor, then
both factors contain the cross edge `a-d`.  Owner uniqueness therefore
forbids the two fork colors from being distinct.

This packages the exact obstruction showing that at most one orbit can take
the one-block branch in the rainbow three-orbit escape. -/
theorem twoIncident_closedOrbitForks_owner_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (source owner₁ owner₂ :
      (secondOrderDefectGraph G).ConnectedComponent)
    (a b c d e f : source.supp)
    (h₁ad : (restrictedComponentOwnerGraph G source owner₁).Adj a d)
    (_h₁ae : (restrictedComponentOwnerGraph G source owner₁).Adj a e)
    (_h₁bd : (restrictedComponentOwnerGraph G source owner₁).Adj b d)
    (_h₁be : (restrictedComponentOwnerGraph G source owner₁).Adj b e)
    (h₂ad : (restrictedComponentOwnerGraph G source owner₂).Adj a d)
    (_h₂af : (restrictedComponentOwnerGraph G source owner₂).Adj a f)
    (_h₂cd : (restrictedComponentOwnerGraph G source owner₂).Adj c d)
    (_h₂cf : (restrictedComponentOwnerGraph G source owner₂).Adj c f) :
    owner₁ = owner₂ := by
  have h₁' :
      (componentOwnerGraph G (secondOrderDefectGraph G) owner₁).Adj a.1 d.1 :=
    h₁ad
  have h₂' :
      (componentOwnerGraph G (secondOrderDefectGraph G) owner₂).Adj a.1 d.1 :=
    h₂ad
  exact ((componentOwnerGraph_adj_iff_owner_eq_of_adj
    G hfree owner₁ h₁' owner₂).mp h₂').symm

/-- Distinct fork colors cannot realize two such incident closed orbits. -/
theorem twoIncident_closedOrbitForks_false
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (source owner₁ owner₂ :
      (secondOrderDefectGraph G).ConnectedComponent)
    (a b c d e f : source.supp) (howners : owner₁ ≠ owner₂)
    (h₁ad : (restrictedComponentOwnerGraph G source owner₁).Adj a d)
    (h₁ae : (restrictedComponentOwnerGraph G source owner₁).Adj a e)
    (h₁bd : (restrictedComponentOwnerGraph G source owner₁).Adj b d)
    (h₁be : (restrictedComponentOwnerGraph G source owner₁).Adj b e)
    (h₂ad : (restrictedComponentOwnerGraph G source owner₂).Adj a d)
    (h₂af : (restrictedComponentOwnerGraph G source owner₂).Adj a f)
    (h₂cd : (restrictedComponentOwnerGraph G source owner₂).Adj c d)
    (h₂cf : (restrictedComponentOwnerGraph G source owner₂).Adj c f) : False :=
  howners (twoIncident_closedOrbitForks_owner_eq
    G hfree source owner₁ owner₂ a b c d e f
      h₁ad h₁ae h₁bd h₁be h₂ad h₂af h₂cd h₂cf)

end

end Erdos85
