import Proofs.Erdos85OrderFortyNineSevenHighT0EmptyVertices
import Proofs.Erdos85OrderFortyNineSevenHighT0PairVertices
import Proofs.Erdos85OrderFortyNineSevenHighT0SingletonCopies

/-!
# Complete indexing of the low vertices in the seven-high t=0 case

The seven empty-support, fourteen singleton-support, and twenty-one
pair-support vertices are disjoint and exhaust all forty-two low vertices.
This packages the actual graph vertex set in exactly the shape used by the
finite quotient and completion models.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

abbrev SevenHighT0LowIndex :=
  Fin 7 ⊕ ((Fin 7 × Fin 2) ⊕ SevenHighT0PairIndex)

private theorem sevenHighT0_nonempty_labeledSupport_not_high
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    {x : Fin 49} (hx : (sevenHighLabeledSupport G e x).Nonempty) :
    x ∉ orderFortyNineHighVertices G := by
  intro hxHigh
  have hz := orderFortyNine_highNeighborCount_eq_zero_of_high
    G hfree hmin (Fintype.card_fin 49) hxHigh
  change (orderFortyNineHighSupport G x).card = 0 at hz
  rw [← sevenHighLabeledSupport_card G e] at hz
  exact hx.ne_empty (Finset.card_eq_zero.mp hz)

def sevenHighT0LowVertex
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7) :
    SevenHighT0LowIndex → {x : Fin 49 // x ∈ orderFortyNineLowVertices G}
  | Sum.inl copy =>
      ⟨sevenHighT0EmptyVertex G hfree hmin hHigh hzero e copy,
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
          sevenHighT0EmptyVertex_not_high
            G hfree hmin hHigh hzero e copy⟩⟩
  | Sum.inr (Sum.inl q) =>
      ⟨sevenHighT0SingletonVertex
          G hfree hmin hHigh hzero e q.1 q.2,
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
          apply sevenHighT0_nonempty_labeledSupport_not_high G hfree hmin e
          rw [sevenHighT0SingletonVertex_support]
          simp⟩⟩
  | Sum.inr (Sum.inr key) =>
      ⟨sevenHighT0PairVertex G hfree hmin hzero e key,
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
          apply sevenHighT0_nonempty_labeledSupport_not_high G hfree hmin e
          rw [sevenHighT0PairVertex_support]
          simp⟩⟩

theorem sevenHighT0LowVertex_injective
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7) :
    Function.Injective
      (sevenHighT0LowVertex G hfree hmin hHigh hzero e) := by
  intro a b hab
  have hv := congrArg Subtype.val hab
  rcases a with a | a <;> rcases b with b | b
  · congr 1
    simp only [sevenHighT0LowVertex] at hv
    exact sevenHighT0EmptyVertex_injective
      G hfree hmin hHigh hzero e hv
  · rcases b with b | b
    · have hs := congrArg (sevenHighLabeledSupport G e) hv
      simp only [sevenHighT0LowVertex] at hs
      rw [sevenHighT0EmptyVertex_support,
        sevenHighT0SingletonVertex_support] at hs
      simp at hs
    · have hs := congrArg (sevenHighLabeledSupport G e) hv
      simp only [sevenHighT0LowVertex] at hs
      rw [sevenHighT0EmptyVertex_support,
        sevenHighT0PairVertex_support] at hs
      have hcard := congrArg Finset.card hs
      simp [ne_of_lt b.2] at hcard
  · rcases a with a | a
    · have hs := congrArg (sevenHighLabeledSupport G e) hv
      simp only [sevenHighT0LowVertex] at hs
      rw [sevenHighT0SingletonVertex_support,
        sevenHighT0EmptyVertex_support] at hs
      simp at hs
    · have hs := congrArg (sevenHighLabeledSupport G e) hv
      simp only [sevenHighT0LowVertex] at hs
      rw [sevenHighT0PairVertex_support,
        sevenHighT0EmptyVertex_support] at hs
      simp at hs
  · rcases a with a | a <;> rcases b with b | b
    · congr 2
      simp only [sevenHighT0LowVertex] at hv
      exact sevenHighT0SingletonVertex_injective
        G hfree hmin hHigh hzero e hv
    · have hs := congrArg (fun x => (sevenHighLabeledSupport G e x).card) hv
      simp only [sevenHighT0LowVertex] at hs
      rw [sevenHighT0SingletonVertex_support,
        sevenHighT0PairVertex_support] at hs
      simp [ne_of_lt b.2] at hs
    · have hs := congrArg (fun x => (sevenHighLabeledSupport G e x).card) hv
      simp only [sevenHighT0LowVertex] at hs
      rw [sevenHighT0PairVertex_support,
        sevenHighT0SingletonVertex_support] at hs
      simp [ne_of_lt a.2] at hs
    · congr 2
      simp only [sevenHighT0LowVertex] at hv
      exact sevenHighT0PairVertex_injective G hfree hmin hzero e hv

private theorem sevenHighT0LowIndex_card :
    Fintype.card SevenHighT0LowIndex = 42 := by
  simp [SevenHighT0LowIndex, sevenHighT0PairIndex_card]

private theorem sevenHighT0LowVertexType_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hHigh : (orderFortyNineHighVertices G).card = 7) :
    Fintype.card {x : Fin 49 // x ∈ orderFortyNineLowVertices G} = 42 := by
  rw [Fintype.card_subtype]
  rw [Finset.filter_mem_eq_inter]
  simp only [Finset.univ_inter]
  rw [orderFortyNineLowVertices, Finset.card_sdiff]
  simp [hHigh]

/-- The concrete `7 + 14 + 21` index map is a bijection onto all low graph
vertices.  In particular, the finite completion model has neither omitted
nor invented a low vertex. -/
noncomputable def sevenHighT0LowVertexEquiv
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7) :
    SevenHighT0LowIndex ≃
      {x : Fin 49 // x ∈ orderFortyNineLowVertices G} :=
  Equiv.ofBijective
    (sevenHighT0LowVertex G hfree hmin hHigh hzero e)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨sevenHighT0LowVertex_injective G hfree hmin hHigh hzero e,
        sevenHighT0LowIndex_card.trans
          (sevenHighT0LowVertexType_card G hHigh).symm⟩)

end


end Erdos85

#print axioms Erdos85.sevenHighT0LowVertex_injective
#print axioms Erdos85.sevenHighT0LowVertexEquiv
