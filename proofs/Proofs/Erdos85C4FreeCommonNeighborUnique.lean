import Proofs.Erdos85Problem

/-!
# Common-neighbor uniqueness in a C4-free graph

This small reusable interface extracts the argument previously duplicated
inside routing proofs.  It is also the exact edge-label uniqueness input for
the witness-indexed relay graph: two distinct endpoints cannot have two
different witnesses adjacent to both.
-/

open SimpleGraph

namespace Erdos85

/-- In a C4-free simple graph, two distinct vertices have at most one common
neighbor. -/
theorem commonNeighbor_unique_of_c4Free
    {V : Type*} {G : SimpleGraph V} (hfree : ¬ containsC4 V G)
    {a b u v : V} (hab : a ≠ b)
    (hau : G.Adj a u) (hbu : G.Adj b u)
    (hav : G.Adj a v) (hbv : G.Adj b v) :
    u = v := by
  by_contra huv
  exact hfree (containsC4_of_rim hau hbu.symm hbv hav.symm hab huv
    (G.ne_of_adj hau).symm (G.ne_of_adj hbu).symm
    (G.ne_of_adj hav).symm (G.ne_of_adj hbv).symm)

/-- Predicate-level form: the common-neighbor fiber of distinct endpoints is
a subsingleton. -/
theorem commonNeighbor_set_subsingleton_of_c4Free
    {V : Type*} {G : SimpleGraph V} (hfree : ¬ containsC4 V G)
    {a b : V} (hab : a ≠ b) :
    Set.Subsingleton {u | G.Adj a u ∧ G.Adj b u} := by
  rintro u ⟨hau, hbu⟩ v ⟨hav, hbv⟩
  exact commonNeighbor_unique_of_c4Free hfree hab hau hbu hav hbv

#print axioms commonNeighbor_unique_of_c4Free
#print axioms commonNeighbor_set_subsingleton_of_c4Free

end Erdos85
