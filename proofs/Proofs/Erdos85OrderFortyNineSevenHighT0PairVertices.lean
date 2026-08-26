import Proofs.Erdos85OrderFortyNineSevenHighT0SingletonCopies

/-!
# Canonical actual pair-support vertices in the seven-high t=0 case

Every unordered pair of high labels is carried by exactly one graph vertex.
This file indexes those twenty-one actual vertices by ordered pairs `a < b`,
parallel to the existing `Fin 7 × Fin 2` indexing of singleton copies.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

abbrev SevenHighT0PairIndex :=
  {p : Fin 7 × Fin 7 // p.1 < p.2}

theorem sevenHighT0PairIndex_card :
    Fintype.card SevenHighT0PairIndex = 21 := by decide

noncomputable def sevenHighT0PairVertexEquiv
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (key : SevenHighT0PairIndex) :
    {x : Fin 49 // sevenHighLabeledSupport G e x =
      {key.1.1, key.1.2}} ≃ Fin 1 :=
  Fintype.equivFinOfCardEq (by
    simpa using sevenHigh_t0_pair_fiber_card_eq_one
      G hfree hmin hzero e key.1.1 key.1.2 (ne_of_lt key.2))

noncomputable def sevenHighT0PairVertex
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (key : SevenHighT0PairIndex) : Fin 49 :=
  ((sevenHighT0PairVertexEquiv
    G hfree hmin hzero e key).symm 0).1

theorem sevenHighT0PairVertex_support
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (key : SevenHighT0PairIndex) :
    sevenHighLabeledSupport G e
      (sevenHighT0PairVertex G hfree hmin hzero e key) =
        {key.1.1, key.1.2} :=
  ((sevenHighT0PairVertexEquiv
    G hfree hmin hzero e key).symm 0).2

/-- Distinct ordered high-label pairs select distinct actual graph vertices. -/
theorem sevenHighT0PairVertex_injective
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7) :
    Function.Injective
      (sevenHighT0PairVertex G hfree hmin hzero e) := by
  intro key key' hvertex
  have hs := congrArg (sevenHighLabeledSupport G e) hvertex
  rw [sevenHighT0PairVertex_support,
    sevenHighT0PairVertex_support] at hs
  have hsSet : ({key.1.1, key.1.2} : Set (Fin 7)) =
      {key'.1.1, key'.1.2} := by
    simpa using congrArg (fun s : Finset (Fin 7) => (s : Set (Fin 7))) hs
  rw [Set.pair_eq_pair_iff] at hsSet
  rcases hsSet with hsame | hswap
  · apply Subtype.ext
    exact Prod.ext hsame.1 hsame.2
  · exfalso
    have hlt := key.2
    have hlt' := key'.2
    omega

end


end Erdos85

#print axioms Erdos85.sevenHighT0PairVertex_support
#print axioms Erdos85.sevenHighT0PairVertex_injective
#print axioms Erdos85.sevenHighT0PairIndex_card
