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

/-- Two distinct boundary vertices of a partner pair cannot themselves be
rook-related.  Thus the ten boundary hits occupy ten distinct blocks for the
partition whose nontrivial blocks are rook partner pairs.

If both boundary vertices meet the same endpoint, the other endpoint is not
needed: the rook law already forbids their common neighbour.  If they meet
opposite endpoints, the source edge and target rook edge form a four-cycle. -/
theorem MuThreeMixedGridCode.partnerPairBoundary_not_rowColumn_adj
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {a b x y : muThreeMixedCell K}
    (hab : C.Adj a b)
    (hx : x ∈ mixedGridPartnerPairBoundary C a b)
    (hy : y ∈ mixedGridPartnerPairBoundary C a b)
    (hCxy : C.Adj x y) :
    ¬ (mixedGridRowColumnGraph K).Adj x y := by
  intro hrook
  have hx' := Finset.mem_sdiff.mp hx
  have hy' := Finset.mem_sdiff.mp hy
  have hxAdj : C.Adj a x ∨ C.Adj b x := by
    simpa only [Finset.mem_union, mem_neighborFinset] using hx'.1
  have hyAdj : C.Adj a y ∨ C.Adj b y := by
    simpa only [Finset.mem_union, mem_neighborFinset] using hy'.1
  have hxa : x ≠ a := by
    intro h
    apply hx'.2
    simp [h]
  have hxb : x ≠ b := by
    intro h
    apply hx'.2
    simp [h]
  have hya : y ≠ a := by
    intro h
    apply hy'.2
    simp [h]
  have hyb : y ≠ b := by
    intro h
    apply hy'.2
    simp [h]
  rcases hxAdj with hax | hbx <;> rcases hyAdj with hay | hby
  · have hzero := code.rowColumn_common_neighbor_card_eq_zero H K C hrook
    have haMem : a ∈ C.neighborFinset x ∩ C.neighborFinset y := by
      exact Finset.mem_inter.mpr
        ⟨(C.mem_neighborFinset x a).mpr hax.symm,
          (C.mem_neighborFinset y a).mpr hay.symm⟩
    rw [Finset.card_eq_zero.mp hzero] at haMem
    exact Finset.notMem_empty a haMem
  · have hle := code.common_neighbor_card_le_one H K C a y hya.symm
    have hxMem : x ∈ C.neighborFinset a ∩ C.neighborFinset y := by
      exact Finset.mem_inter.mpr
        ⟨(C.mem_neighborFinset a x).mpr hax,
          (C.mem_neighborFinset y x).mpr hCxy.symm⟩
    have hbMem : b ∈ C.neighborFinset a ∩ C.neighborFinset y := by
      exact Finset.mem_inter.mpr
        ⟨(C.mem_neighborFinset a b).mpr hab,
          (C.mem_neighborFinset y b).mpr hby.symm⟩
    exact hxb (Finset.card_le_one.mp hle x hxMem b hbMem)
  · have hle := code.common_neighbor_card_le_one H K C b y hyb.symm
    have hxMem : x ∈ C.neighborFinset b ∩ C.neighborFinset y := by
      exact Finset.mem_inter.mpr
        ⟨(C.mem_neighborFinset b x).mpr hbx,
          (C.mem_neighborFinset y x).mpr hCxy.symm⟩
    have haMem : a ∈ C.neighborFinset b ∩ C.neighborFinset y := by
      exact Finset.mem_inter.mpr
        ⟨(C.mem_neighborFinset b a).mpr hab.symm,
          (C.mem_neighborFinset y a).mpr hay.symm⟩
    exact hxa (Finset.card_le_one.mp hle x hxMem a haMem)
  · have hzero := code.rowColumn_common_neighbor_card_eq_zero H K C hrook
    have hbMem : b ∈ C.neighborFinset x ∩ C.neighborFinset y := by
      exact Finset.mem_inter.mpr
        ⟨(C.mem_neighborFinset x b).mpr hbx.symm,
          (C.mem_neighborFinset y b).mpr hby.symm⟩
    rw [Finset.card_eq_zero.mp hzero] at hbMem
    exact Finset.notMem_empty b hbMem

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.partnerPairBoundary_card_eq_ten
#print axioms Erdos85.MuThreeMixedGridCode.partnerPairBoundary_not_rowColumn_adj
