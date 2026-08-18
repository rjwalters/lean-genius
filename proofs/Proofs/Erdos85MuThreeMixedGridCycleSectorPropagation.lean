import Proofs.Erdos85MuThreeMixedGridCode

/-!
# Propagation of the H/K sector along an H-cycle

The cycle-compatibility field says that each connected component of the
bipartite two-factor `H` is wholly contained in `K` or wholly disjoint from
`K`.  Here it is exposed in witness-driven forms usable by the mixed-grid
permutation analysis.
-/

open SimpleGraph

namespace Erdos85

/-- One common `H ∩ K` edge forces every `H`-edge in its component into
`K`. -/
theorem MuThreeMixedGridCode.cycleComponent_all_K_of_edge
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (c : (relationBipartiteGraph H).ConnectedComponent)
    {x : X} {y : Y} (hH : H x y) (hK : K x y)
    (hxc : Sum.inl x ∈ c.supp) :
    ∀ x' y', H x' y' → Sum.inl x' ∈ c.supp → K x' y' := by
  rcases code.cycle_compatible c with hall | hnone
  · exact hall
  · exact False.elim (hnone x y hH hxc hK)

/-- One occupied `H \ K` cell forces every `H`-edge in its component outside
`K`. -/
theorem MuThreeMixedGridCode.cycleComponent_all_not_K_of_cell
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (c : (relationBipartiteGraph H).ConnectedComponent)
    (u : muThreeMixedCell K) (hH : H u.1.1 u.1.2)
    (huc : Sum.inl u.1.1 ∈ c.supp) :
    ∀ x y, H x y → Sum.inl x ∈ c.supp → ¬ K x y := by
  rcases code.cycle_compatible c with hall | hnone
  · exact False.elim (u.2 (hall u.1.1 u.1.2 hH huc))
  · exact hnone

/-- Equivalently, the truth value of `K` is constant on all `H`-edges whose
left endpoints lie in one `H`-component. -/
theorem MuThreeMixedGridCode.K_iff_K_of_H_edges_same_component
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (c : (relationBipartiteGraph H).ConnectedComponent)
    {x x' : X} {y y' : Y}
    (hH : H x y) (hH' : H x' y')
    (hxc : Sum.inl x ∈ c.supp) (hx'c : Sum.inl x' ∈ c.supp) :
    K x y ↔ K x' y' := by
  rcases code.cycle_compatible c with hall | hnone
  · exact iff_of_true (hall x y hH hxc) (hall x' y' hH' hx'c)
  · exact iff_of_false (hnone x y hH hxc) (hnone x' y' hH' hx'c)

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.cycleComponent_all_K_of_edge
#print axioms Erdos85.MuThreeMixedGridCode.cycleComponent_all_not_K_of_cell
#print axioms
  Erdos85.MuThreeMixedGridCode.K_iff_K_of_H_edges_same_component
