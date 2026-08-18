import Proofs.Erdos85DifferenceArrayParity

/-!
# Graph-facing parity of diagonal anchors

This assembles the intrinsic difference-array parity theorem with the
inverse-pair description of graph diagonal blocks.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

theorem odd_graph_diagonalAnchorMultiplicity_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r : ℕ} [NeZero r]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr3 : 3 ≤ r) (hrOdd : Odd r)
    (u : (secondOrderDefectGraph G).ConnectedComponent → ZMod r → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hsep : ∀ {c e : (secondOrderDefectGraph G).ConnectedComponent},
      c ≠ e → ∀ x y, u c x ≠ u e y)
    (hodd : Odd (Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent))
    (h : ZMod r) :
    Odd (anchorMultiplicity
      (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c)) h) ↔
      2 * h ∈ allowedCycleDifferences r := by
  let C := (secondOrderDefectGraph G).ConnectedComponent
  let A : C → C → Finset (ZMod r) :=
    fun c e ↦ graphCycleBlockZeroSupport G (u c) (u e)
  have hcomm := adjMatrix_comm_secondOrderDefect_of_even
    G hfree hd heven hmin hcard
  have hexcess : ∀ c, ∑ e,
      (A c e).card * ((A c e).card - 1) = r - 3 := by
    intro c
    simpa only [A] using
      secondOrder_equalComponents_zeroRowSupport_excess
        G hfree hd heven hmin hcard hr3 u hu huRange c
  have hsymm : ∀ c e,
      orderedDifferenceSet (A c e) = orderedDifferenceSet (A e c) := by
    intro c e
    exact orderedDifferenceSet_graphCycleBlockZeroSupport_symm
      hr3 hrOdd G (secondOrderDefectGraph G) (u c) (u e)
        (hu c) (hu e) hcomm (huD c) (huD e)
  have hleave : ∀ c, unusedOrderedDifferences (A c) = {1, -1} := by
    intro c
    exact unusedOrderedDifferences_graphCycleBlockZeroSupport_eq_one_negOne
      G hfree hd heven hmin hcard hr3 hrOdd (u c) u (hu c) (huD c)
        hu huD hsep hcomm (hexcess c)
  have hdisj : ∀ c, ∀ {e f : C}, e ≠ f →
      Disjoint (orderedDifferenceSet (A c e))
        (orderedDifferenceSet (A c f)) := by
    intro c e f hef
    have heOrient := graph_equalOddCycleBlock_orientation hr3 hrOdd G
      (secondOrderDefectGraph G) (u c) (u e) (hu c) (hu e)
        hcomm (huD c) (huD e)
    have hfOrient := graph_equalOddCycleBlock_orientation hr3 hrOdd G
      (secondOrderDefectGraph G) (u c) (u f) (hu c) (hu f)
        hcomm (huD c) (huD f)
    simpa only [A, graphCycleBlockZeroSupport] using
      (orderedDifferenceSet_zeroRowSupport_disjoint_of_c4Free_orientations
        G hfree (u c) (u e) (u f) (hu c) (hsep hef)
          heOrient hfOrient)
  have hdiffParity :=
    odd_card_diagonal_orderedDifference_occurrences_iff
      hr3 A hsymm hleave hdisj hodd (2 * h)
  have hfilter :
      (Finset.univ.filter fun c ↦ h ∈ A c c) =
        Finset.univ.filter fun c ↦
          2 * h ∈ orderedDifferenceSet (A c c) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact mem_graphCycleBlockZeroSupport_self_iff_two_mul_difference
      G hfree hd heven hmin hcard hr3 hrOdd c (u c) (hu c)
        (huRange c) (huD c) h
  unfold anchorMultiplicity
  change Odd ((Finset.univ.filter fun c ↦ h ∈ A c c).card) ↔ _
  rw [hfilter]
  exact hdiffParity

end

end Erdos85
