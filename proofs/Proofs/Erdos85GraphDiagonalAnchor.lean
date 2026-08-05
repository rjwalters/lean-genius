import Proofs.Erdos85DiagonalAnchorParity
import Proofs.Erdos85DifferenceArrayBoundary

/-!
# Graph-facing diagonal anchors

The zero-row support of a diagonal block between an odd defect cycle and
itself is inverse closed.  In the circulant orientation this follows from
symmetry of the graph; in the reverse-circulant orientation looplessness
forces the whole block to vanish.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

theorem negFinset_graphCycleBlockZeroSupport_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d r : ℕ} [NeZero r]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr3 : 3 ≤ r) (hrOdd : Odd r)
    (u : ZMod r → V) (hu : Function.Injective u)
    (huD : ∀ x, (secondOrderDefectGraph G).neighborFinset (u x) =
      {u (x - 1), u (x + 1)}) :
    negFinset (graphCycleBlockZeroSupport G u u) =
      graphCycleBlockZeroSupport G u u := by
  let D := secondOrderDefectGraph G
  let B : Matrix (ZMod r) (ZMod r) ℤ :=
    fun x y ↦ G.adjMatrix ℤ (u x) (u y)
  have hcomm := adjMatrix_comm_secondOrderDefect_of_even
    G hfree hd heven hmin hcard
  have hOrient := graph_equalOddCycleBlock_orientation
    hr3 hrOdd G D u u hu hu hcomm huD huD
  have hcolrow : zeroColumnSupport B = zeroRowSupport B := by
    ext z
    simp only [zeroColumnSupport, zeroRowSupport, Finset.mem_filter,
      Finset.mem_univ, true_and, B, SimpleGraph.adjMatrix_apply]
    simp [G.adj_comm]
  rcases hOrient with htrans | hreverse
  · have hcolneg :=
      zeroColumnSupport_eq_neg_zeroRowSupport_of_translationInvariant B htrans
    change negFinset (zeroRowSupport B) = zeroRowSupport B
    rw [← hcolneg, hcolrow]
  · have hdiag : ∀ z, B z z = 0 := by
      intro z
      simp [B, SimpleGraph.adjMatrix_apply]
    have hzero := oddCycle_reverseTranslationInvariant_zero_of_diagonal_zero
      hrOdd B hreverse hdiag
    have hrow : zeroRowSupport B = ∅ := by
      ext z
      simp [zeroRowSupport, hzero]
    change negFinset (zeroRowSupport B) = zeroRowSupport B
    rw [hrow]
    simp [negFinset]

theorem graphCycleBlockZeroSupport_self_card_le_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r : ℕ} [NeZero r]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr3 : 3 ≤ r) (hrOdd : Odd r)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (u : ZMod r → V) (hu : Function.Injective u)
    (huRange : Set.range u = c.supp)
    (huD : ∀ x, (secondOrderDefectGraph G).neighborFinset (u x) =
      {u (x - 1), u (x + 1)}) :
    (graphCycleBlockZeroSupport G u u).card ≤ 2 := by
  rw [card_graphCycleBlockZeroSupport_eq_componentQuotient
    G hfree hd heven hmin hcard c c u u hu huRange huRange]
  exact secondOrder_equalOddCycleComponent_diagonal_le_two
    G hfree hd heven hmin hcard hr3 hrOdd c u hu huRange huD

theorem graphCycleBlockZeroSupport_self_zero_not_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : ℕ} [NeZero r] (u : ZMod r → V) :
    (0 : ZMod r) ∉ graphCycleBlockZeroSupport G u u := by
  simp [graphCycleBlockZeroSupport, zeroRowSupport,
    SimpleGraph.adjMatrix_apply]

/-- A graph diagonal anchor is detected exactly by its doubled ordered
difference. -/
theorem mem_graphCycleBlockZeroSupport_self_iff_two_mul_difference
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r : ℕ} [NeZero r]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr3 : 3 ≤ r) (hrOdd : Odd r)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (u : ZMod r → V) (hu : Function.Injective u)
    (huRange : Set.range u = c.supp)
    (huD : ∀ x, (secondOrderDefectGraph G).neighborFinset (u x) =
      {u (x - 1), u (x + 1)}) (h : ZMod r) :
    h ∈ graphCycleBlockZeroSupport G u u ↔
      2 * h ∈ orderedDifferenceSet (graphCycleBlockZeroSupport G u u) := by
  apply mem_iff_two_mul_mem_orderedDifferenceSet_of_inverse_pair hrOdd
  · exact negFinset_graphCycleBlockZeroSupport_self
      G hfree hd heven hmin hcard hr3 hrOdd u hu huD
  · exact graphCycleBlockZeroSupport_self_card_le_two
      G hfree hd heven hmin hcard hr3 hrOdd c u hu huRange huD
  · exact graphCycleBlockZeroSupport_self_zero_not_mem G u

end

end Erdos85
