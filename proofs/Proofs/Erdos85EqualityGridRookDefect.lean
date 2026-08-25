import Proofs.Erdos85BinarySquareRegularParity

/-!
# The defect graph avoids the rook graph of an equality grid

At a saturated grid, each used point has at most one coordinate on each side.
Consequently cells in a common row or column are distinct graph vertices, and
their shared coordinate is a common neighbor in the original graph.  They are
therefore nonadjacent in the second-order defect graph.
-/

open Finset

namespace Erdos85

noncomputable section

/-- Two equality-grid cells with the same `Z` coordinate and different `P`
coordinates form a nonedge of the second-order defect graph. -/
theorem equalityGrid_same_left_not_secondOrderDefect_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (Q P : Finset V)
    (hPdeg : ∀ x ∈ Q, (P.filter fun p => G.Adj p x).card ≤ 1)
    {z p p' x y : V}
    (hxQ : x ∈ Q) (hyQ : y ∈ Q)
    (hpP : p ∈ P) (hp'P : p' ∈ P) (hpp' : p ≠ p')
    (hzx : G.Adj z x) (hzy : G.Adj z y)
    (hpx : G.Adj p x) (hp'y : G.Adj p' y) :
    ¬ (secondOrderDefectGraph G).Adj x y := by
  have hxy : x ≠ y := by
    intro h
    subst y
    have hpMem : p ∈ P.filter fun a => G.Adj a x :=
      Finset.mem_filter.mpr ⟨hpP, hpx⟩
    have hp'Mem : p' ∈ P.filter fun a => G.Adj a x :=
      Finset.mem_filter.mpr ⟨hp'P, hp'y⟩
    exact hpp' (Finset.card_le_one.mp (hPdeg x hxQ) p hpMem p' hp'Mem)
  exact not_secondOrderDefect_adj_of_commonNeighbor G hfree hxy hzx.symm hzy.symm

/-- Two equality-grid cells with the same `P` coordinate and different `Z`
coordinates form a nonedge of the second-order defect graph. -/
theorem equalityGrid_same_right_not_secondOrderDefect_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (Q Z : Finset V)
    (hZdeg : ∀ x ∈ Q, (Z.filter fun z => G.Adj z x).card ≤ 1)
    {z z' p x y : V}
    (hxQ : x ∈ Q) (hyQ : y ∈ Q)
    (hzZ : z ∈ Z) (hz'Z : z' ∈ Z) (hzz' : z ≠ z')
    (hzx : G.Adj z x) (hz'y : G.Adj z' y)
    (hpx : G.Adj p x) (hpy : G.Adj p y) :
    ¬ (secondOrderDefectGraph G).Adj x y := by
  have hxy : x ≠ y := by
    intro h
    subst y
    have hzMem : z ∈ Z.filter fun a => G.Adj a x :=
      Finset.mem_filter.mpr ⟨hzZ, hzx⟩
    have hz'Mem : z' ∈ Z.filter fun a => G.Adj a x :=
      Finset.mem_filter.mpr ⟨hz'Z, hz'y⟩
    exact hzz' (Finset.card_le_one.mp (hZdeg x hxQ) z hzMem z' hz'Mem)
  exact not_secondOrderDefect_adj_of_commonNeighbor G hfree hxy hpx.symm hpy.symm

end

end Erdos85

#print axioms Erdos85.equalityGrid_same_left_not_secondOrderDefect_adj
#print axioms Erdos85.equalityGrid_same_right_not_secondOrderDefect_adj
