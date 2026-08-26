import Proofs.Erdos85OrderFortyNineSevenHighZeroFiber

/-!
# Canonical actual empty-support vertices in the seven-high t=0 case

The aligned empty-low fiber has exactly seven members.  This file chooses
those actual graph vertices, indexed by `Fin 7`, and records their aligned
key, empty high support, low status, and injectivity.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

def sevenHighT0EmptyVertexEquiv
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7) :
    {x : Fin 49 // sevenHighGraphAlignedKey G e x = (none, ∅)} ≃ Fin 7 :=
  Fintype.equivFinOfCardEq
    (sevenHigh_t0_aligned_emptyLow_fiber_card_eq_seven
      G hfree hmin hHigh hzero e)

def sevenHighT0EmptyVertex
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (copy : Fin 7) : Fin 49 :=
  ((sevenHighT0EmptyVertexEquiv
    G hfree hmin hHigh hzero e).symm copy).1

theorem sevenHighT0EmptyVertex_key
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (copy : Fin 7) :
    sevenHighGraphAlignedKey G e
      (sevenHighT0EmptyVertex G hfree hmin hHigh hzero e copy) =
        (none, ∅) :=
  ((sevenHighT0EmptyVertexEquiv
    G hfree hmin hHigh hzero e).symm copy).2

theorem sevenHighT0EmptyVertex_not_high
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (copy : Fin 7) :
    sevenHighT0EmptyVertex G hfree hmin hHigh hzero e copy ∉
      orderFortyNineHighVertices G := by
  intro hx
  have hkey := congrArg Prod.fst
    (sevenHighT0EmptyVertex_key G hfree hmin hHigh hzero e copy)
  simp [sevenHighGraphAlignedKey, hx] at hkey

theorem sevenHighT0EmptyVertex_support
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (copy : Fin 7) :
    sevenHighLabeledSupport G e
      (sevenHighT0EmptyVertex G hfree hmin hHigh hzero e copy) = ∅ := by
  have hkey := congrArg Prod.snd
    (sevenHighT0EmptyVertex_key G hfree hmin hHigh hzero e copy)
  simpa [sevenHighGraphAlignedKey,
    sevenHighT0EmptyVertex_not_high G hfree hmin hHigh hzero e copy] using hkey

theorem sevenHighT0EmptyVertex_injective
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7) :
    Function.Injective
      (sevenHighT0EmptyVertex G hfree hmin hHigh hzero e) := by
  intro a b hab
  apply (sevenHighT0EmptyVertexEquiv
    G hfree hmin hHigh hzero e).symm.injective
  apply Subtype.ext
  exact hab

end


end Erdos85

#print axioms Erdos85.sevenHighT0EmptyVertex_key
#print axioms Erdos85.sevenHighT0EmptyVertex_not_high
#print axioms Erdos85.sevenHighT0EmptyVertex_support
#print axioms Erdos85.sevenHighT0EmptyVertex_injective
