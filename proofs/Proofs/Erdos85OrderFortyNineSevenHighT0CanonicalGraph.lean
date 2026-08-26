import Proofs.Erdos85OrderFortyNineSevenHighT0IndexedProfiles

/-!
# The complete canonical graph in the seven-high t=0 case

The seven labeled high vertices and the complete `7E + 14S + 21P` low
index form a canonical 49-element vertex type.  This file proves that its
concrete map to the original graph is a bijection and transports the whole
graph along that bijection.  It is the semantic carrier for the single
canonical completion CNF.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

abbrev SevenHighT0CanonicalIndex := Fin 7 ⊕ SevenHighT0LowIndex

def sevenHighT0CanonicalVertex
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7) :
    SevenHighT0CanonicalIndex → Fin 49
  | Sum.inl w => (e.symm w).1
  | Sum.inr i =>
      (sevenHighT0LowVertex G hfree hmin hHigh hzero e i).1

theorem sevenHighT0CanonicalVertex_injective
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7) :
    Function.Injective
      (sevenHighT0CanonicalVertex G hfree hmin hHigh hzero e) := by
  intro a b hab
  rcases a with a | a <;> rcases b with b | b
  · simp only [sevenHighT0CanonicalVertex] at hab
    congr 1
    apply e.symm.injective
    exact Subtype.ext hab
  · exfalso
    simp only [sevenHighT0CanonicalVertex] at hab
    have haHigh : (e.symm a).1 ∈ orderFortyNineHighVertices G :=
      (e.symm a).2
    have hbNotHigh :
        (sevenHighT0LowVertex G hfree hmin hHigh hzero e b).1 ∉
          orderFortyNineHighVertices G :=
      (Finset.mem_sdiff.mp
        (sevenHighT0LowVertex G hfree hmin hHigh hzero e b).2).2
    exact hbNotHigh (hab ▸ haHigh)
  · exfalso
    simp only [sevenHighT0CanonicalVertex] at hab
    have hbHigh : (e.symm b).1 ∈ orderFortyNineHighVertices G :=
      (e.symm b).2
    have haNotHigh :
        (sevenHighT0LowVertex G hfree hmin hHigh hzero e a).1 ∉
          orderFortyNineHighVertices G :=
      (Finset.mem_sdiff.mp
        (sevenHighT0LowVertex G hfree hmin hHigh hzero e a).2).2
    exact haNotHigh (hab.symm ▸ hbHigh)
  · congr 1
    simp only [sevenHighT0CanonicalVertex] at hab
    apply sevenHighT0LowVertex_injective G hfree hmin hHigh hzero e
    exact Subtype.ext hab

private theorem sevenHighT0CanonicalIndex_card :
    Fintype.card SevenHighT0CanonicalIndex = 49 := by
  simp [SevenHighT0CanonicalIndex, SevenHighT0LowIndex,
    sevenHighT0PairIndex_card]

/-- The canonical 49-index names every original graph vertex exactly once. -/
noncomputable def sevenHighT0CanonicalVertexEquiv
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7) :
    SevenHighT0CanonicalIndex ≃ Fin 49 :=
  Equiv.ofBijective
    (sevenHighT0CanonicalVertex G hfree hmin hHigh hzero e)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨sevenHighT0CanonicalVertex_injective
          G hfree hmin hHigh hzero e,
        sevenHighT0CanonicalIndex_card.trans (Fintype.card_fin 49).symm⟩)

/-- The entire original graph pulled back to the canonical index. -/
def sevenHighT0CanonicalGraph
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7) :
    SimpleGraph SevenHighT0CanonicalIndex :=
  G.comap (sevenHighT0CanonicalVertex G hfree hmin hHigh hzero e)

instance sevenHighT0CanonicalGraph_adj_decidable
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7) :
    DecidableRel (sevenHighT0CanonicalGraph
      G hfree hmin hHigh hzero e).Adj := by
  intro i j
  change Decidable (G.Adj _ _)
  infer_instance

theorem sevenHighT0CanonicalGraph_adj_iff
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (i j : SevenHighT0CanonicalIndex) :
    (sevenHighT0CanonicalGraph G hfree hmin hHigh hzero e).Adj i j ↔
      G.Adj
        (sevenHighT0CanonicalVertex G hfree hmin hHigh hzero e i)
        (sevenHighT0CanonicalVertex G hfree hmin hHigh hzero e j) := Iff.rfl

theorem sevenHighT0CanonicalGraph_not_containsC4
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7) :
    ¬ containsC4 SevenHighT0CanonicalIndex
      (sevenHighT0CanonicalGraph G hfree hmin hHigh hzero e) := by
  rintro ⟨f, hf, hadj⟩
  apply hfree
  refine ⟨sevenHighT0CanonicalVertex G hfree hmin hHigh hzero e ∘ f,
    (sevenHighT0CanonicalVertex_injective
      G hfree hmin hHigh hzero e).comp hf, ?_⟩
  intro i j hij
  exact hadj i j hij

/-- A canonical high label is adjacent to a canonical low index exactly when
that label belongs to the low vertex's labeled high support. -/
theorem sevenHighT0CanonicalGraph_high_low_adj_iff
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (w : Fin 7) (i : SevenHighT0LowIndex) :
    (sevenHighT0CanonicalGraph G hfree hmin hHigh hzero e).Adj
        (Sum.inl w) (Sum.inr i) ↔
      w ∈ sevenHighLabeledSupport G e
        (sevenHighT0LowVertex G hfree hmin hHigh hzero e i) := by
  change G.Adj (e.symm w).1
      (sevenHighT0LowVertex G hfree hmin hHigh hzero e i) ↔ _
  rw [mem_sevenHighLabeledSupport_iff]
  exact G.adj_comm _ _

theorem sevenHighT0CanonicalGraph_high_high_not_adj
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (w z : Fin 7) :
    ¬ (sevenHighT0CanonicalGraph G hfree hmin hHigh hzero e).Adj
      (Sum.inl w) (Sum.inl z) := by
  intro hwz
  change G.Adj (e.symm w).1 (e.symm z).1 at hwz
  have hzMem : z ∈ sevenHighLabeledSupport G e (e.symm w).1 :=
    (mem_sevenHighLabeledSupport_iff G e _ _).2 hwz
  have hcard := orderFortyNine_highNeighborCount_eq_zero_of_high
    G hfree hmin (Fintype.card_fin 49) (e.symm w).2
  change (orderFortyNineHighSupport G (e.symm w).1).card = 0 at hcard
  rw [← sevenHighLabeledSupport_card G e] at hcard
  rw [Finset.card_eq_zero.mp hcard] at hzMem
  simp at hzMem

theorem sevenHighT0CanonicalGraph_high_empty_not_adj
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (w copy : Fin 7) :
    ¬ (sevenHighT0CanonicalGraph G hfree hmin hHigh hzero e).Adj
      (Sum.inl w) (Sum.inr (Sum.inl copy)) := by
  rw [sevenHighT0CanonicalGraph_high_low_adj_iff]
  simp only [sevenHighT0LowVertex, sevenHighT0EmptyVertex_support]
  simp

theorem sevenHighT0CanonicalGraph_high_singleton_adj_iff
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (w : Fin 7) (q : Fin 7 × Fin 2) :
    (sevenHighT0CanonicalGraph G hfree hmin hHigh hzero e).Adj
      (Sum.inl w) (Sum.inr (Sum.inr (Sum.inl q))) ↔ w = q.1 := by
  rw [sevenHighT0CanonicalGraph_high_low_adj_iff]
  simp only [sevenHighT0LowVertex, sevenHighT0SingletonVertex_support]
  simp

theorem sevenHighT0CanonicalGraph_high_pair_adj_iff
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (w : Fin 7) (key : SevenHighT0PairIndex) :
    (sevenHighT0CanonicalGraph G hfree hmin hHigh hzero e).Adj
      (Sum.inl w) (Sum.inr (Sum.inr (Sum.inr key))) ↔
        w = key.1.1 ∨ w = key.1.2 := by
  rw [sevenHighT0CanonicalGraph_high_low_adj_iff]
  simp only [sevenHighT0LowVertex, sevenHighT0PairVertex_support]
  simp

end


end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalVertex_injective
#print axioms Erdos85.sevenHighT0CanonicalVertexEquiv
#print axioms Erdos85.sevenHighT0CanonicalGraph_adj_iff
#print axioms Erdos85.sevenHighT0CanonicalGraph_not_containsC4
#print axioms Erdos85.sevenHighT0CanonicalGraph_high_low_adj_iff
#print axioms Erdos85.sevenHighT0CanonicalGraph_high_high_not_adj
#print axioms Erdos85.sevenHighT0CanonicalGraph_high_empty_not_adj
#print axioms Erdos85.sevenHighT0CanonicalGraph_high_singleton_adj_iff
#print axioms Erdos85.sevenHighT0CanonicalGraph_high_pair_adj_iff
