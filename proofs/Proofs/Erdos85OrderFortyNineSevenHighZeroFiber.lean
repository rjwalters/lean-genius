import Proofs.Erdos85OrderFortyNineSevenHighFiberLabeling

/-!
# Fiber census for the empty seven-high triple system

When `t=0`, every low high-support has size at most two.  Globally there are
seven empty, fourteen singleton, and twenty-one pair supports; locally at
each high point there are exactly two singleton and six pair supports.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

theorem sevenHigh_t0_global_incidence
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0) :
    orderFortyNineHighIncidenceCount G 0 = 7 ∧
    orderFortyNineHighIncidenceCount G 1 = 14 ∧
    orderFortyNineHighIncidenceCount G 2 = 21 := by
  have hp := orderFortyNine_highIncidence_profile_of_seven_high
    G hfree hmin (Fintype.card_fin 49) hHigh
  dsimp only at hp
  omega

theorem sevenHigh_t0_no_triple_neighbor
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    {v : Fin 49} (hv : v ∈ orderFortyNineHighVertices G) :
    ((G.neighborFinset v).filter fun x =>
      (orderFortyNineHighSupport G x).card = 3).card = 0 := by
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxN := (Finset.mem_filter.mp hx).1
  have hx3 := (Finset.mem_filter.mp hx).2
  have hxLow : x ∈ orderFortyNineLowVertices G := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ x, ?_⟩
    intro hxHigh
    have hx8 := (Finset.mem_filter.mp hxHigh).2
    have hv8 := (Finset.mem_filter.mp hv).2
    have hadj : G.Adj v x := by
      simpa [SimpleGraph.mem_neighborFinset] using hxN
    have hx7 := orderFortyNine_neighbor_degree_seven_of_degreeEight
      G hfree hmin (Fintype.card_fin 49) hv8 hadj
    omega
  have hxGlobal : x ∈ (orderFortyNineLowVertices G).filter fun y =>
      (G.neighborFinset y ∩ orderFortyNineHighVertices G).card = 3 := by
    apply Finset.mem_filter.mpr
    simpa [orderFortyNineHighSupport] using And.intro hxLow hx3
  have hempty : ((orderFortyNineLowVertices G).filter fun y =>
      (G.neighborFinset y ∩ orderFortyNineHighVertices G).card = 3) = ∅ := by
    apply Finset.card_eq_zero.mp
    exact hzero
  rw [hempty] at hxGlobal
  simp at hxGlobal

theorem sevenHigh_t0_local_incidence
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    {v : Fin 49} (hv : v ∈ orderFortyNineHighVertices G) :
    ((G.neighborFinset v).filter fun x =>
      (orderFortyNineHighSupport G x).card = 1).card = 2 ∧
    ((G.neighborFinset v).filter fun x =>
      (orderFortyNineHighSupport G x).card = 2).card = 6 := by
  have hv8 : G.degree v = 8 := (Finset.mem_filter.mp hv).2
  have hp := orderFortyNine_highNeighborhood_profile_of_seven_high
    G hfree hmin (Fintype.card_fin 49) hHigh hv8
  dsimp only at hp
  have h3 := sevenHigh_t0_no_triple_neighbor G hfree hmin hzero hv
  omega

theorem sevenHigh_t0_exists_pair_support
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (a b : Fin 7) (hab : a ≠ b) :
    ∃ x : Fin 49, sevenHighLabeledSupport G e x = {a, b} := by
  have hvab : (e.symm a).1 ≠ (e.symm b).1 := by
    intro h
    apply hab
    apply e.symm.injective
    exact Subtype.ext h
  obtain ⟨x, hx, _⟩ := orderFortyNine_existsUnique_pairBlock_of_highs
    G hfree hmin (Fintype.card_fin 49)
      (e.symm a).2 (e.symm b).2 hvab
  have hxCard : (orderFortyNineHighSupport G x).card = 2 := by
    rcases hx.2.2.2 with h2 | h3
    · exact h2
    · exfalso
      have hxLow : x ∈ orderFortyNineLowVertices G := by
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_univ x, ?_⟩
        intro hxHigh
        have hx8 := (Finset.mem_filter.mp hxHigh).2
        omega
      have hxGlobal : x ∈ (orderFortyNineLowVertices G).filter fun y =>
          (G.neighborFinset y ∩ orderFortyNineHighVertices G).card = 3 := by
        exact Finset.mem_filter.mpr ⟨hxLow, by
          simpa [orderFortyNineHighSupport] using h3⟩
      have hempty : ((orderFortyNineLowVertices G).filter fun y =>
          (G.neighborFinset y ∩ orderFortyNineHighVertices G).card = 3) = ∅ :=
        Finset.card_eq_zero.mp hzero
      rw [hempty] at hxGlobal
      simp at hxGlobal
  have hcardL : (sevenHighLabeledSupport G e x).card = 2 := by
    rw [sevenHighLabeledSupport_card]
    exact hxCard
  have hsub : ({a, b} : Finset (Fin 7)) ⊆
      sevenHighLabeledSupport G e x := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with hw | hw
    · subst w
      exact (mem_sevenHighLabeledSupport_iff G e x _).mpr hx.1.symm
    · subst w
      exact (mem_sevenHighLabeledSupport_iff G e x _).mpr hx.2.1.symm
  refine ⟨x, ?_⟩
  have hpCard : ({a, b} : Finset (Fin 7)).card = 2 := by simp [hab]
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

theorem sevenHigh_t0_pair_fiber_card_eq_one
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (a b : Fin 7) (hab : a ≠ b) :
    Fintype.card {x : Fin 49 // sevenHighLabeledSupport G e x = {a, b}} = 1 := by
  obtain ⟨x, hx⟩ := sevenHigh_t0_exists_pair_support
    G hfree hmin hzero e a b hab
  have hcard := sevenHighLabeledSupport_fiber_card_eq_one
    G hfree e x (by rw [hx]; simp [hab])
  simpa [hx] using hcard

theorem sevenHigh_t0_singleton_fiber_card_eq_two
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (w : Fin 7) :
    Fintype.card {x : Fin 49 // sevenHighLabeledSupport G e x = {w}} = 2 := by
  rw [Fintype.card_subtype]
  let v : Fin 49 := (e.symm w).1
  have hv : v ∈ orderFortyNineHighVertices G := (e.symm w).2
  have hset : (Finset.univ.filter fun x : Fin 49 =>
      sevenHighLabeledSupport G e x = {w}) =
      (G.neighborFinset v).filter fun x =>
        (orderFortyNineHighSupport G x).card = 1 := by
    ext x
    constructor
    · intro hx
      have hs := (Finset.mem_filter.mp hx).2
      apply Finset.mem_filter.mpr
      constructor
      · have hwMem : w ∈ sevenHighLabeledSupport G e x := by simp [hs]
        simpa [v, SimpleGraph.mem_neighborFinset, G.adj_comm] using
          (mem_sevenHighLabeledSupport_iff G e x w).mp hwMem
      · rw [← sevenHighLabeledSupport_card G e x, hs]
        simp
    · intro hx
      have hxN := (Finset.mem_filter.mp hx).1
      have hxCard := (Finset.mem_filter.mp hx).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ x, ?_⟩
      have hwMem : w ∈ sevenHighLabeledSupport G e x := by
        apply (mem_sevenHighLabeledSupport_iff G e x w).mpr
        simpa [v, SimpleGraph.mem_neighborFinset, G.adj_comm] using hxN
      have hcard : (sevenHighLabeledSupport G e x).card = 1 := by
        rw [sevenHighLabeledSupport_card]
        exact hxCard
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
      have hwz : w = z := by
        rw [hz] at hwMem
        simpa using hwMem
      simp [hz, hwz]
  rw [hset]
  exact (sevenHigh_t0_local_incidence
    G hfree hmin hHigh hzero hv).1

end

end Erdos85
