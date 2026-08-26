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

def sevenHighT0CommonSingletonCopies
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (x y : Fin 49) : Finset (Fin 7 × Fin 2) :=
  Finset.univ.filter fun q =>
    G.Adj x (sevenHighT0SingletonVertex
      G hfree hmin hHigh hzero e q.1 q.2) ∧
    G.Adj y (sevenHighT0SingletonVertex
      G hfree hmin hHigh hzero e q.1 q.2)

/-- Two distinct vertices share at most one of the fourteen actual singleton
copies.  This is the sound copy-indexed form of the `C₄` compatibility rule. -/
theorem sevenHighT0CommonSingletonCopies_card_le_one
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    {x y : Fin 49} (hxy : x ≠ y) :
    (sevenHighT0CommonSingletonCopies
      G hfree hmin hHigh hzero e x y).card ≤ 1 := by
  let actual := (G.neighborFinset x ∩ G.neighborFinset y).filter fun z =>
    (orderFortyNineHighSupport G z).card = 1
  let vertex := fun q : Fin 7 × Fin 2 =>
    sevenHighT0SingletonVertex G hfree hmin hHigh hzero e q.1 q.2
  have hmap : ∀ q ∈ sevenHighT0CommonSingletonCopies
      G hfree hmin hHigh hzero e x y, vertex q ∈ actual := by
    intro q hq
    have hq' := (Finset.mem_filter.mp hq).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_inter.mpr ?_, ?_⟩
    · simpa [SimpleGraph.mem_neighborFinset, vertex] using hq'
    · rw [← sevenHighLabeledSupport_card G e]
      rw [sevenHighT0SingletonVertex_support]
      simp
  have hinj : Set.InjOn vertex
      (sevenHighT0CommonSingletonCopies
        G hfree hmin hHigh hzero e x y : Set (Fin 7 × Fin 2)) :=
    (sevenHighT0SingletonVertex_injective
      G hfree hmin hHigh hzero e).injOn
  have hcard := Finset.card_le_card_of_injOn vertex hmap hinj
  exact hcard.trans
    (sevenHigh_t0_actualSingleton_commonNeighbor_card_le_one G hfree hxy)

/-- If the two roots already share a non-singleton actual neighbor, their
copy-indexed common-singleton set is empty. -/
theorem sevenHighT0CommonSingletonCopies_eq_empty_of_common_nonSingleton
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    {x y z : Fin 49} (hxy : x ≠ y)
    (hzx : G.Adj z x) (hzy : G.Adj z y)
    (hzNotSingleton : (orderFortyNineHighSupport G z).card ≠ 1) :
    sevenHighT0CommonSingletonCopies
      G hfree hmin hHigh hzero e x y = ∅ := by
  have hempty :=
    sevenHigh_t0_actualSingleton_commonNeighbor_eq_empty_of_common_nonSingleton
      G hfree hxy hzx hzy hzNotSingleton
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hq' := (Finset.mem_filter.mp hq).2
  have hactual :
      sevenHighT0SingletonVertex G hfree hmin hHigh hzero e q.1 q.2 ∈
        (G.neighborFinset x ∩ G.neighborFinset y).filter fun w =>
          (orderFortyNineHighSupport G w).card = 1 := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_inter.mpr ?_, ?_⟩
    · simpa [SimpleGraph.mem_neighborFinset] using hq'
    · rw [← sevenHighLabeledSupport_card G e]
      rw [sevenHighT0SingletonVertex_support]
      simp
  rw [hempty] at hactual
  simp at hactual

end

end Erdos85

#print axioms Erdos85.sevenHighT0SingletonVertex_support
#print axioms Erdos85.sevenHighT0SingletonVertex_injective_copy
#print axioms Erdos85.sevenHighT0SingletonVertex_injective
#print axioms Erdos85.sevenHighT0CommonSingletonCopies_card_le_one
#print axioms Erdos85.sevenHighT0CommonSingletonCopies_eq_empty_of_common_nonSingleton
