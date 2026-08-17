import Proofs.Erdos85RoutingOwnerRainbowExactColors

/-! # Shared edges identify restricted owner colors -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Two restricted owner factors cannot both contain the same edge unless
their owner components are equal. -/
theorem restrictedOwner_eq_of_shared_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (source owner₁ owner₂ :
      (secondOrderDefectGraph G).ConnectedComponent)
    {x y : source.supp}
    (h₁ : (restrictedComponentOwnerGraph G source owner₁).Adj x y)
    (h₂ : (restrictedComponentOwnerGraph G source owner₂).Adj x y) :
    owner₁ = owner₂ := by
  have h₁' :
      (componentOwnerGraph G (secondOrderDefectGraph G) owner₁).Adj x.1 y.1 :=
    h₁
  have h₂' :
      (componentOwnerGraph G (secondOrderDefectGraph G) owner₂).Adj x.1 y.1 :=
    h₂
  exact ((componentOwnerGraph_adj_iff_owner_eq_of_adj
    G hfree owner₁ h₁' owner₂).mp h₂').symm

/-- In particular, two repeated-fork `K₂,₂` witnesses whose displayed
cross edges overlap have the same fork color.  The unused three edges are
kept in the interface so a six-vertex orbit classification can apply this
lemma directly to its two fork packages. -/
theorem repeatedFork_colors_eq_of_shared_crossEdge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (source owner₁ owner₂ :
      (secondOrderDefectGraph G).ConnectedComponent)
    {x y z r s t : source.supp}
    (h₁xr : (restrictedComponentOwnerGraph G source owner₁).Adj x r)
    (_h₁xs : (restrictedComponentOwnerGraph G source owner₁).Adj x s)
    (_h₁yr : (restrictedComponentOwnerGraph G source owner₁).Adj y r)
    (_h₁ys : (restrictedComponentOwnerGraph G source owner₁).Adj y s)
    (h₂xr : (restrictedComponentOwnerGraph G source owner₂).Adj x r)
    (_h₂xt : (restrictedComponentOwnerGraph G source owner₂).Adj x t)
    (_h₂zr : (restrictedComponentOwnerGraph G source owner₂).Adj z r)
    (_h₂zt : (restrictedComponentOwnerGraph G source owner₂).Adj z t) :
    owner₁ = owner₂ :=
  restrictedOwner_eq_of_shared_edge G hfree source owner₁ owner₂ h₁xr h₂xr

end

end Erdos85
