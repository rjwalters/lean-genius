import Proofs.Erdos85MuThreeMixedGridRoutePermutation

/-!
# Disjoint route codewords for rook-related sources

The general C4 bound permits one agreement between two row-route codewords.
For two source cells in one row or column, the rook law strengthens this to
zero: an agreement would be a common exterior neighbour of a rook pair.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Row-route codewords of distinct rook-related cells have no agreement. -/
theorem mixedGridRouteAgreementRows_eq_empty_of_rook
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u v : muThreeMixedCell K) (huv : u ≠ v)
    (hrook : u.1.1 = v.1.1 ∨ u.1.2 = v.1.2) :
    mixedGridRouteAgreementRows H K C code u v = ∅ := by
  ext x
  constructor
  · intro hx
    obtain ⟨hux, hvx, hagree⟩ := (Finset.mem_filter.mp hx).2
    let w := mixedGridRowRoute H K C code u x hux
    have huw : C.Adj u w := mixedGridRowRoute_adj H K C code u x hux
    have hvw : C.Adj v w := by
      change C.Adj v (mixedGridRowRoute H K C code u x hux)
      rw [hagree]
      exact mixedGridRowRoute_adj H K C code v x hvx
    have hsep := code.rook w u v (C.adj_symm huw) (C.adj_symm hvw) huv
    exact (hrook.elim hsep.1 hsep.2).elim
  · simp

/-- Pointwise form for two distinct cells in a common column.  Their allowed
row domains coincide, and the selected exterior cells are always different. -/
theorem mixedGridRowRoute_ne_of_sameColumn
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u v : muThreeMixedCell K) (huv : u ≠ v)
    (hcolumn : u.1.2 = v.1.2) (x : X)
    (hux : ¬ H x u.1.2) (hvx : ¬ H x v.1.2) :
    mixedGridRowRoute H K C code u x hux ≠
      mixedGridRowRoute H K C code v x hvx := by
  intro hagree
  have hx : x ∈ mixedGridRouteAgreementRows H K C code u v := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hux, hvx, hagree⟩⟩
  rw [mixedGridRouteAgreementRows_eq_empty_of_rook H K C code u v huv
    (Or.inr hcolumn)] at hx
  simpa using hx

/-- Coordinate-permutation form of route disjointness: two distinct sources
in one column assign different output columns to every commonly allowed row. -/
theorem mixedGridRowPermutationFun_ne_of_sameColumn
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u v : muThreeMixedCell K) (huv : u ≠ v)
    (hcolumn : u.1.2 = v.1.2) (x : X)
    (hux : ¬ H x u.1.2) (hvx : ¬ H x v.1.2) :
    (mixedGridRowPermutationFun H K C code u ⟨x, hux⟩).1 ≠
      (mixedGridRowPermutationFun H K C code v ⟨x, hvx⟩).1 := by
  intro hcol
  apply mixedGridRowRoute_ne_of_sameColumn H K C code u v huv hcolumn x hux hvx
  apply Subtype.ext
  apply Prod.ext
  · rw [mixedGridRowRoute_row H K C code u x hux,
      mixedGridRowRoute_row H K C code v x hvx]
  · exact hcol

end

end Erdos85

#print axioms Erdos85.mixedGridRouteAgreementRows_eq_empty_of_rook
#print axioms Erdos85.mixedGridRowRoute_ne_of_sameColumn
#print axioms Erdos85.mixedGridRowPermutationFun_ne_of_sameColumn
