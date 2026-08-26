import Proofs.Erdos85OrderFortyNineSevenHighT0ActualSingletonCompatibility

/-!
# The fourteen actual singleton-support vertices

In the seven-high empty-triple stratum each high label is carried by exactly
two distinct singleton-support vertices.  This file chooses those two actual
vertices, indexed by `Fin 2`, and proves that the resulting `Fin 7 × Fin 2`
parametrization is injective.  A finite quotient model must use these copies,
not collapse them to the seven high labels.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

def sevenHighT0SingletonCopyEquiv
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (w : Fin 7) :
    {x : Fin 49 // sevenHighLabeledSupport G e x = {w}} ≃ Fin 2 :=
  Fintype.equivFinOfCardEq
    (sevenHigh_t0_singleton_fiber_card_eq_two
      G hfree hmin hHigh hzero e w)

def sevenHighT0SingletonVertex
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (w : Fin 7) (copy : Fin 2) : Fin 49 :=
  ((sevenHighT0SingletonCopyEquiv
    G hfree hmin hHigh hzero e w).symm copy).1

theorem sevenHighT0SingletonVertex_support
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (w : Fin 7) (copy : Fin 2) :
    sevenHighLabeledSupport G e
      (sevenHighT0SingletonVertex G hfree hmin hHigh hzero e w copy) = {w} :=
  ((sevenHighT0SingletonCopyEquiv
    G hfree hmin hHigh hzero e w).symm copy).2

/-- The two copies of a fixed label are distinct actual graph vertices. -/
theorem sevenHighT0SingletonVertex_injective_copy
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (w : Fin 7) :
    Function.Injective
      (sevenHighT0SingletonVertex G hfree hmin hHigh hzero e w) := by
  intro a b hab
  apply (sevenHighT0SingletonCopyEquiv
    G hfree hmin hHigh hzero e w).symm.injective
  apply Subtype.ext
  exact hab

/-- All fourteen label/copy pairs name distinct actual graph vertices. -/
theorem sevenHighT0SingletonVertex_injective
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7) :
    Function.Injective (fun q : Fin 7 × Fin 2 =>
      sevenHighT0SingletonVertex
        G hfree hmin hHigh hzero e q.1 q.2) := by
  intro a b hab
  rcases a with ⟨aw, ac⟩
  rcases b with ⟨bw, bc⟩
  have hsupport := congrArg (sevenHighLabeledSupport G e) hab
  rw [sevenHighT0SingletonVertex_support,
    sevenHighT0SingletonVertex_support] at hsupport
  have hlabel : aw = bw := Finset.singleton_injective hsupport
  subst bw
  have hcopy : ac = bc := sevenHighT0SingletonVertex_injective_copy
    G hfree hmin hHigh hzero e aw (by simpa using hab)
  cases hcopy
  rfl

end

end Erdos85

#print axioms Erdos85.sevenHighT0SingletonVertex_support
#print axioms Erdos85.sevenHighT0SingletonVertex_injective_copy
#print axioms Erdos85.sevenHighT0SingletonVertex_injective
