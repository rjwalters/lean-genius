import Proofs.Erdos85CommonNeighborPigeonhole

/-!
# Pointwise common-neighbour exclusions

Small graph-facing consequences of `C4`-freeness used to remove impossible
branches before invoking finite certificates.
-/

open SimpleGraph

namespace Erdos85

/-- If `u` and `a` are distinct neighbours of `v`, then every other
neighbour of `u` is forbidden from `a`.  Otherwise `v` and that neighbour
would be two common neighbours of `u` and `a`. -/
theorem not_adj_of_adj_common_root_and_adj_partner
    {V : Type*} (G : SimpleGraph V)
    (hfree : ¬ containsC4 V G) {v u a b : V}
    (hua : u ≠ a) (hvb : v ≠ b)
    (hvu : G.Adj v u) (hva : G.Adj v a) (hub : G.Adj u b) :
    ¬ G.Adj a b := by
  intro hab
  exact hfree (containsC4_of_two_common hua hvb
    hvu hva hub.symm hab.symm)

end Erdos85
