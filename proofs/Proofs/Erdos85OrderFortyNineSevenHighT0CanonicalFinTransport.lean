import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalSemanticStructure
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalCnfSatisfaction
import Proofs.Erdos85OrderFortyNineAlignedBooleanBridge
import Proofs.Erdos85OrderFortyNineHighIncidenceCensus
import Proofs.Erdos85OrderFortyNineSevenHighT0LocalQuotientCapacity
import Proofs.Erdos85OrderFortyNineSevenHighT0GlobalQuotientParity

/-!
# Transport canonical H7/T0 semantics to `Fin 49`

The reviewed quotient-capacity theorems are stated on `Fin 49`, whereas the
canonical SAT semantics use the structured type `Fin 7 ⊕ SevenHighT0LowIndex`.
This file packages the exact relabeling and the invariants needed to apply
those theorems without rebuilding their proofs on the sum type.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

def sevenHighT0CanonicalFinGraph
    (H : SimpleGraph SevenHighT0CanonicalIndex) : SimpleGraph (Fin 49) :=
  orderFortyNineRelabeledGraph H sevenHighT0CanonicalIndexEquiv.symm

instance sevenHighT0CanonicalFinGraph_decidableAdj
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj] :
    DecidableRel (sevenHighT0CanonicalFinGraph H).Adj := fun i j =>
  inferInstanceAs (Decidable (H.Adj
    (sevenHighT0CanonicalIndexEquiv i)
    (sevenHighT0CanonicalIndexEquiv j)))

@[simp] theorem sevenHighT0CanonicalFinGraph_adj
    (H : SimpleGraph SevenHighT0CanonicalIndex) (i j : Fin 49) :
    (sevenHighT0CanonicalFinGraph H).Adj i j ↔
      H.Adj (sevenHighT0CanonicalIndexEquiv i)
        (sevenHighT0CanonicalIndexEquiv j) := by
  rfl

theorem sevenHighT0CanonicalFinGraph_degree
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (i : Fin 49) :
    (sevenHighT0CanonicalFinGraph H).degree i =
      H.degree (sevenHighT0CanonicalIndexEquiv i) := by
  exact orderFortyNineRelabeledGraph_degree H
    sevenHighT0CanonicalIndexEquiv.symm i

theorem sevenHighT0CanonicalFinGraph_not_containsC4
    (H : SimpleGraph SevenHighT0CanonicalIndex)
    (hfree : ¬ containsC4 SevenHighT0CanonicalIndex H) :
    ¬ containsC4 (Fin 49) (sevenHighT0CanonicalFinGraph H) := by
  exact orderFortyNineRelabeledGraph_not_containsC4 H
    sevenHighT0CanonicalIndexEquiv.symm hfree

theorem sevenHighT0CanonicalFinGraph_mem_highVertices_iff
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (i : Fin 49) :
    i ∈ orderFortyNineHighVertices (sevenHighT0CanonicalFinGraph H) ↔
      sevenHighT0CanonicalIndexEquiv i ∈ orderFortyNineHighVertices H := by
  simp only [orderFortyNineHighVertices, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [sevenHighT0CanonicalFinGraph_degree]

theorem sevenHighT0CanonicalFinGraph_highVertices_card
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj] :
    (orderFortyNineHighVertices (sevenHighT0CanonicalFinGraph H)).card =
      (orderFortyNineHighVertices H).card := by
  apply Finset.card_bij
    (fun i _ => sevenHighT0CanonicalIndexEquiv i)
  · intro i hi
    exact (sevenHighT0CanonicalFinGraph_mem_highVertices_iff H i).mp hi
  · intro a ha b hb hab
    exact sevenHighT0CanonicalIndexEquiv.injective hab
  · intro x hx
    refine ⟨sevenHighT0CanonicalIndexEquiv.symm x, ?_, by simp⟩
    exact (sevenHighT0CanonicalFinGraph_mem_highVertices_iff H _).mpr
      (by simpa using hx)

theorem sevenHighT0CanonicalFinGraph_highSupport_card
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (i : Fin 49) :
    (orderFortyNineHighSupport (sevenHighT0CanonicalFinGraph H) i).card =
      (orderFortyNineHighSupport H
        (sevenHighT0CanonicalIndexEquiv i)).card := by
  apply Finset.card_bij
    (fun j _ => sevenHighT0CanonicalIndexEquiv j)
  · intro j hj
    rw [orderFortyNineHighSupport, Finset.mem_inter] at hj ⊢
    exact ⟨by
        have hadj := (sevenHighT0CanonicalFinGraph_adj H i j).mp
          (by simpa using hj.1)
        simpa using hadj,
      (sevenHighT0CanonicalFinGraph_mem_highVertices_iff H j).mp hj.2⟩
  · intro a ha b hb hab
    exact sevenHighT0CanonicalIndexEquiv.injective hab
  · intro x hx
    refine ⟨sevenHighT0CanonicalIndexEquiv.symm x, ?_, by simp⟩
    rw [orderFortyNineHighSupport, Finset.mem_inter] at hx ⊢
    exact ⟨by
        simpa using (sevenHighT0CanonicalFinGraph_adj H i
          (sevenHighT0CanonicalIndexEquiv.symm x)).mpr
          (by simpa using hx.1),
      (sevenHighT0CanonicalFinGraph_mem_highVertices_iff H _).mpr
        (by simpa using hx.2)⟩

theorem sevenHighT0CanonicalFinGraph_highIncidenceCount
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (k : Nat) :
    orderFortyNineHighIncidenceCount (sevenHighT0CanonicalFinGraph H) k =
      orderFortyNineHighIncidenceCount H k := by
  unfold orderFortyNineHighIncidenceCount orderFortyNineLowVertices
  apply Finset.card_bij
    (fun i _ => sevenHighT0CanonicalIndexEquiv i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
      true_and] at hi ⊢
    exact ⟨fun h => hi.1
        ((sevenHighT0CanonicalFinGraph_mem_highVertices_iff H i).mpr h),
      (sevenHighT0CanonicalFinGraph_highSupport_card H i).symm.trans hi.2⟩
  · intro a ha b hb hab
    exact sevenHighT0CanonicalIndexEquiv.injective hab
  · intro x hx
    refine ⟨sevenHighT0CanonicalIndexEquiv.symm x, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
      true_and] at hx ⊢
    refine ⟨?_, ?_⟩
    · intro h
      exact hx.1 (by
        simpa using (sevenHighT0CanonicalFinGraph_mem_highVertices_iff H _).mp h)
    · calc
        (orderFortyNineHighSupport (sevenHighT0CanonicalFinGraph H)
            (sevenHighT0CanonicalIndexEquiv.symm x)).card =
            (orderFortyNineHighSupport H
              (sevenHighT0CanonicalIndexEquiv
                (sevenHighT0CanonicalIndexEquiv.symm x))).card :=
          sevenHighT0CanonicalFinGraph_highSupport_card H _
        _ = (orderFortyNineHighSupport H x).card := by simp
        _ = k := hx.2

/-- Complete hypothesis package needed by the existing `Fin 49` quotient
theorems, recovered solely from canonical completion semantics. -/
theorem SevenHighT0CanonicalCompletionSemantics.finGraph_hypotheses
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H) :
    (¬ containsC4 (Fin 49) (sevenHighT0CanonicalFinGraph H)) ∧
    (∀ i : Fin 49, 7 ≤ (sevenHighT0CanonicalFinGraph H).degree i) ∧
    (orderFortyNineHighVertices (sevenHighT0CanonicalFinGraph H)).card = 7 ∧
    orderFortyNineHighIncidenceCount (sevenHighT0CanonicalFinGraph H) 3 = 0 := by
  refine ⟨sevenHighT0CanonicalFinGraph_not_containsC4 H semantics.c4Free,
    ?_, ?_, ?_⟩
  · intro i
    rw [sevenHighT0CanonicalFinGraph_degree]
    exact semantics.minDegree_seven _
  · rw [sevenHighT0CanonicalFinGraph_highVertices_card]
    exact semantics.highVertices_card
  · rw [sevenHighT0CanonicalFinGraph_highIncidenceCount]
    exact semantics.highIncidenceCount_three

/-- Reuse the reviewed global quotient theorem on the transported canonical
graph.  This is the exact `6 ≤ F ≤ 10` input for empty-mask admissibility. -/
theorem SevenHighT0CanonicalCompletionSemantics.finGraph_internalEmptyEdge_bounds
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H) :
    6 ≤ sevenHighT0InternalEdgeCount (sevenHighT0CanonicalFinGraph H) 0 ∧
      sevenHighT0InternalEdgeCount (sevenHighT0CanonicalFinGraph H) 0 ≤ 10 := by
  let G := sevenHighT0CanonicalFinGraph H
  letI : DecidableRel (antipodalGraph G).Adj := Classical.decRel _
  letI : DecidableRel (triangleFreeEdgeGraph G).Adj := Classical.decRel _
  obtain ⟨hfree, hmin, hHigh, hzero⟩ := semantics.finGraph_hypotheses
  exact sevenHigh_t0_internalEmptyEdge_parameter_bounds
    G hfree hmin hHigh hzero

/-- Pointwise empty-root capacity bound on the transported graph. -/
theorem SevenHighT0CanonicalCompletionSemantics.finGraph_emptyRoot_bound
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H)
    {y : Fin 49}
    (hy : (sevenHighT0CanonicalFinGraph H).degree y = 7) :
    ((((sevenHighT0CanonicalFinGraph H).neighborFinset y).filter fun x =>
      (orderFortyNineHighSupport (sevenHighT0CanonicalFinGraph H) x).card = 0
      ).filter fun x =>
        x ∉ orderFortyNineHighVertices (sevenHighT0CanonicalFinGraph H)).card ≤
      3 := by
  let G := sevenHighT0CanonicalFinGraph H
  letI : DecidableRel (antipodalGraph G).Adj := Classical.decRel _
  letI : DecidableRel (triangleFreeEdgeGraph G).Adj := Classical.decRel _
  obtain ⟨hfree, hmin, hHigh, hzero⟩ := semantics.finGraph_hypotheses
  exact sevenHigh_t0_emptyRoot_lowEmptyNeighbor_bound
    G hfree hmin hHigh hzero hy

theorem SevenHighT0CanonicalCompletionSemantics.mem_finGraph_emptyFiber_iff
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H)
    (i : Fin 49) :
    i ∈ sevenHighT0LowSupportFiber (sevenHighT0CanonicalFinGraph H) 0 ↔
      ∃ w : Fin 7,
        sevenHighT0CanonicalIndexEquiv i = Sum.inr (Sum.inl w) := by
  rw [sevenHighT0LowSupportFiber, Finset.mem_filter]
  simp only [orderFortyNineLowVertices, Finset.mem_sdiff, Finset.mem_univ,
    true_and]
  rw [sevenHighT0CanonicalFinGraph_mem_highVertices_iff,
    sevenHighT0CanonicalFinGraph_highSupport_card]
  generalize hx : sevenHighT0CanonicalIndexEquiv i = x
  rcases x with w | j
  · simp [semantics.mem_highVertices_iff]
  · rw [semantics.low_highSupport_card]
    rcases j with w | j
    · simp [sevenHighT0LowIndexSupportCard,
        semantics.mem_highVertices_iff]
    · rcases j with j | j
      · simp [sevenHighT0LowIndexSupportCard,
          semantics.mem_highVertices_iff]
      · simp [sevenHighT0LowIndexSupportCard,
          semantics.mem_highVertices_iff]

noncomputable def SevenHighT0CanonicalCompletionSemantics.finGraphEmptyFiberEquiv
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H) :
    Fin 7 ≃ {i : Fin 49 //
      i ∈ sevenHighT0LowSupportFiber (sevenHighT0CanonicalFinGraph H) 0} where
  toFun w := ⟨sevenHighT0CanonicalIndexEquiv.symm (Sum.inr (Sum.inl w)),
    semantics.mem_finGraph_emptyFiber_iff _ |>.2 ⟨w, by simp⟩⟩
  invFun i := Classical.choose
    ((semantics.mem_finGraph_emptyFiber_iff i.1).1 i.2)
  left_inv w := by
    have hw := Classical.choose_spec
      ((semantics.mem_finGraph_emptyFiber_iff
        (sevenHighT0CanonicalIndexEquiv.symm
          (Sum.inr (Sum.inl w)))).1
        (semantics.mem_finGraph_emptyFiber_iff _ |>.2 ⟨w, by simp⟩))
    simpa using hw.symm
  right_inv i := by
    apply Subtype.ext
    have hw := Classical.choose_spec
      ((semantics.mem_finGraph_emptyFiber_iff i.1).1 i.2)
    simpa using congrArg sevenHighT0CanonicalIndexEquiv.symm hw.symm

noncomputable def SevenHighT0CanonicalCompletionSemantics.finGraphEmptyFiberIso
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H) :
    H.comap (fun w : Fin 7 => Sum.inr (Sum.inl w)) ≃g
      (sevenHighT0CanonicalFinGraph H).induce
        (↑(sevenHighT0LowSupportFiber
          (sevenHighT0CanonicalFinGraph H) 0) : Set (Fin 49)) where
  toEquiv := semantics.finGraphEmptyFiberEquiv
  map_rel_iff' := by
    intro a b
    change H.Adj
        (sevenHighT0CanonicalIndexEquiv
          (sevenHighT0CanonicalIndexEquiv.symm (Sum.inr (Sum.inl a))))
        (sevenHighT0CanonicalIndexEquiv
          (sevenHighT0CanonicalIndexEquiv.symm (Sum.inr (Sum.inl b)))) ↔
      H.Adj (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl b))
    simp

theorem SevenHighT0CanonicalCompletionSemantics.finGraph_internalEmptyEdgeCount_eq
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H) :
    sevenHighT0InternalEdgeCount (sevenHighT0CanonicalFinGraph H) 0 =
      (H.comap (fun w : Fin 7 => Sum.inr (Sum.inl w))).edgeFinset.card := by
  rw [sevenHighT0InternalEdgeCount]
  exact semantics.finGraphEmptyFiberIso.card_edgeFinset_eq.symm

end

end Erdos85

#print axioms Erdos85.SevenHighT0CanonicalCompletionSemantics.finGraph_hypotheses
#print axioms Erdos85.SevenHighT0CanonicalCompletionSemantics.finGraph_internalEmptyEdge_bounds
