import Proofs.Erdos85SquareOrderSectorProfile
import Proofs.Erdos85ConflictDegreeAccounting

/-!
# High-neighborhood parity at square order

At exact square order, a degree-`d+1` vertex in a tight-edge-cover core has
conflict degree `d²-1`, so its conflict neighborhood exhausts every other
vertex.  Its ordinary open neighborhood is consequently 1-regular.  Hence it
has even cardinality `d+1`, forcing `d` odd.  In particular an even-parameter
square-order core is regular.
-/

open SimpleGraph Finset

namespace Erdos85

noncomputable section

theorem squareOrder_degree_commonNeighborConflict_of_degree_succ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 2 ≤ d)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) {x : V} (hx : G.degree x = d + 1) :
    (commonNeighborConflict G).degree x = Fintype.card V - 1 := by
  rw [degree_commonNeighborConflict_eq_degree_mul_pred_of_nontight
    G hfree hcover x (by omega), hx, hcard]
  have hpred : d - 1 + 1 = d := Nat.sub_add_cancel (by omega)
  have hsucc : d + 1 = (d - 1) + 2 := by omega
  have hid : (d + 1) * (d - 1) + 1 = d * d := by
    calc
      (d + 1) * (d - 1) + 1 = ((d - 1) + 2) * (d - 1) + 1 := by rw [hsucc]
      _ = ((d - 1) + 1) * ((d - 1) + 1) := by ring
      _ = d * d := by rw [hpred]
  omega

theorem squareOrder_conflictNeighborFinset_of_degree_succ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 2 ≤ d)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) {x : V} (hx : G.degree x = d + 1) :
    (commonNeighborConflict G).neighborFinset x = Finset.univ.erase x := by
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    have hyAdj := ((commonNeighborConflict G).mem_neighborFinset x y).mp hy
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact hyAdj.ne.symm
  · rw [(commonNeighborConflict G).card_neighborFinset_eq_degree,
      squareOrder_degree_commonNeighborConflict_of_degree_succ
        G hfree hd hcover hcard hx,
      Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]

theorem squareOrder_localNeighborhood_degree_eq_one_of_degree_succ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 2 ≤ d)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) {x : V} (hx : G.degree x = d + 1)
    (y : {z : V // z ∈ G.neighborSet x}) :
    (G.induce (G.neighborSet x)).degree y = 1 := by
  rw [degree_induce_neighborSet_eq_card_common]
  have hle := common_le_one_of_not_containsC4 hfree x y.1
    (G.ne_of_adj y.2)
  have hconflictSet := squareOrder_conflictNeighborFinset_of_degree_succ
    G hfree hd hcover hcard hx
  have hyErase : y.1 ∈ (Finset.univ : Finset V).erase x := by
    simp [G.ne_of_adj y.2 |>.symm]
  have hyConflictMem :
      y.1 ∈ (commonNeighborConflict G).neighborFinset x := by
    rw [hconflictSet]
    exact hyErase
  have hnonempty :=
    (((commonNeighborConflict G).mem_neighborFinset x y.1).mp
      hyConflictMem).2
  have hpos : 0 < (G.neighborFinset x ∩ G.neighborFinset y.1).card :=
    Finset.card_pos.mpr hnonempty
  omega

theorem squareOrder_odd_of_exists_degree_succ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 2 ≤ d)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {x : V} (hx : G.degree x = d + 1) : Odd d := by
  let H := G.induce (G.neighborSet x)
  have hlocal : ∀ y : {z : V // z ∈ G.neighborSet x}, H.degree y = 1 :=
    squareOrder_localNeighborhood_degree_eq_one_of_degree_succ
      G hfree hd hcover hcard hx
  have hhand := H.sum_degrees_eq_twice_card_edges
  have hsum : (∑ y : {z : V // z ∈ G.neighborSet x}, H.degree y) =
      Fintype.card {z : V // z ∈ G.neighborSet x} := by
    simp_rw [hlocal]
    simp
  change (∑ y : {z : V // z ∈ G.neighborSet x}, H.degree y) =
    2 * H.edgeFinset.card at hhand
  rw [hsum] at hhand
  have hcardNeighbor :
      Fintype.card {z : V // z ∈ G.neighborSet x} = d + 1 := by
    rw [SimpleGraph.card_neighborSet_eq_degree, hx]
  rw [hcardNeighbor] at hhand
  refine Nat.not_even_iff_odd.mp ?_
  intro heven
  rcases heven with ⟨k, hk⟩
  omega

/-- The nonregular square-order sector is empty for even parameters. -/
theorem squareOrder_regular_of_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 2 ≤ d) (heven : Even d)
    (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) :
    ∀ x : V, G.degree x = d := by
  intro x
  rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
      G hfree hd hmin hcover hcard x with hx | hx
  · exact hx
  · exact False.elim ((Nat.not_even_iff_odd.mpr
      (squareOrder_odd_of_exists_degree_succ
        G hfree hd hcover hcard hx)) heven)

end

end Erdos85
