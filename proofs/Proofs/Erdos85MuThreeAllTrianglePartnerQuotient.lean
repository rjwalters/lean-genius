import Proofs.Erdos85MuThreeMixedGridSquarePartition

/-!
# Exterior boundary of a partner pair

A partner edge joins two cells in one row or column.  The rook law says that
its endpoints have no common exterior neighbour.  Since the exterior graph is
six-regular, their two neighbourhoods are disjoint and have twelve vertices
in total.  Removing the two endpoints of the partner edge leaves exactly ten
outward incidences.

Together with `partnerCrossEdges_card_le_one`, this is the local degree count
behind the quotient of the mixed grid by either partner matching: a partner
pair sends ten edges out, and at most one can land in any other partner pair.
-/

open SimpleGraph

namespace Erdos85

/-- Exterior neighbours of either endpoint of a pair, excluding the pair
itself. -/
def mixedGridPartnerPairBoundary
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {K : X → Y → Prop} [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (a b : muThreeMixedCell K) : Finset (muThreeMixedCell K) :=
  (C.neighborFinset a ∪ C.neighborFinset b) \ {a, b}

/-- **Partner-pair outward degree ten.**  Every partner edge has exactly ten
exterior neighbours outside its two endpoints. -/
theorem MuThreeMixedGridCode.partnerPairBoundary_card_eq_ten
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {a b : muThreeMixedCell K}
    (hab : C.Adj a b)
    (hrook : (mixedGridRowColumnGraph K).Adj a b) :
    (mixedGridPartnerPairBoundary C a b).card = 10 := by
  classical
  have hcommon := code.rowColumn_common_neighbor_card_eq_zero H K C hrook
  have hdisjoint : Disjoint (C.neighborFinset a) (C.neighborFinset b) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    exact Finset.card_eq_zero.mp hcommon
  have hna : (C.neighborFinset a).card = 6 := by
    rw [C.card_neighborFinset_eq_degree, code.degree_eq_six H K C a]
  have hnb : (C.neighborFinset b).card = 6 := by
    rw [C.card_neighborFinset_eq_degree, code.degree_eq_six H K C b]
  have hpair : ({a, b} : Finset (muThreeMixedCell K)).card = 2 := by
    simp [C.ne_of_adj hab]
  have hsubset : ({a, b} : Finset (muThreeMixedCell K)) ⊆
      C.neighborFinset a ∪ C.neighborFinset b := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with hua | hub
    · subst u
      exact Finset.mem_union_right _ ((C.mem_neighborFinset b a).mpr hab.symm)
    · subst u
      exact Finset.mem_union_left _ ((C.mem_neighborFinset a b).mpr hab)
  rw [mixedGridPartnerPairBoundary, Finset.card_sdiff,
    Finset.inter_eq_left.mpr hsubset, hpair,
    Finset.card_union_of_disjoint hdisjoint, hna, hnb]

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.partnerPairBoundary_card_eq_ten
