import Proofs.Erdos85OrderFortyNineSevenHighT0LocalQuotientCapacity

/-!
# Global quotient sums in the seven-high empty-triple case

This file sums the graph-valid pointwise law `P = E + k` over each low
high-support fiber.  The resulting constants `42`, `14`, and `0` are the
three balance rows consumed by the one-parameter quotient arithmetic.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

def sevenHighT0LowSupportFiber
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj] (k : Nat) :
    Finset (Fin 49) :=
  (orderFortyNineLowVertices G).filter fun y =>
    (orderFortyNineHighSupport G y).card = k

def sevenHighT0PairNeighborCount
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj] (y : Fin 49) : Nat :=
  ((G.neighborFinset y).filter fun x =>
    (orderFortyNineHighSupport G x).card = 2).card

def sevenHighT0LowEmptyNeighborCount
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj] (y : Fin 49) : Nat :=
  (((G.neighborFinset y).filter fun x =>
    (orderFortyNineHighSupport G x).card = 0).filter fun x =>
      x ∉ orderFortyNineHighVertices G).card

/-- Directed adjacency incidences from the low support-`a` fiber to the low
support-`b` fiber. -/
def sevenHighT0DirectedIncidence
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj] (a b : Nat) : Nat :=
  ∑ y ∈ sevenHighT0LowSupportFiber G a,
    ((G.neighborFinset y).filter fun x =>
      x ∈ sevenHighT0LowSupportFiber G b).card

private theorem degree_eq_seven_of_mem_lowSupportFiber
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    {k : Nat} {y : Fin 49} (hy : y ∈ sevenHighT0LowSupportFiber G k) :
    G.degree y = 7 := by
  have hyLow := (Finset.mem_filter.mp hy).1
  have hyNotHigh := (Finset.mem_sdiff.mp hyLow).2
  rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin (Fintype.card_fin 49) y with hy7 | hy8
  · exact hy7
  · exact False.elim (hyNotHigh (by
      simp [orderFortyNineHighVertices, hy8]))

private theorem mem_low_of_support_card_eq_two
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    {x : Fin 49} (hx : (orderFortyNineHighSupport G x).card = 2) :
    x ∈ orderFortyNineLowVertices G := by
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ x, ?_⟩
  intro hxHigh
  have hxZero := orderFortyNine_highNeighborCount_eq_zero_of_high
    G hfree hmin (Fintype.card_fin 49) hxHigh
  change (orderFortyNineHighSupport G x).card = 0 at hxZero
  omega

private theorem pairNeighborCount_eq_fiberIncidence
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (y : Fin 49) :
    sevenHighT0PairNeighborCount G y =
      ((G.neighborFinset y).filter fun x =>
        x ∈ sevenHighT0LowSupportFiber G 2).card := by
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hxy, hxTwo⟩
    exact ⟨hxy, Finset.mem_filter.mpr
      ⟨mem_low_of_support_card_eq_two G hfree hmin hxTwo, hxTwo⟩⟩
  · rintro ⟨hxy, hxFiber⟩
    exact ⟨hxy, (Finset.mem_filter.mp hxFiber).2⟩

private theorem lowEmptyNeighborCount_eq_fiberIncidence
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj] (y : Fin 49) :
    sevenHighT0LowEmptyNeighborCount G y =
      ((G.neighborFinset y).filter fun x =>
        x ∈ sevenHighT0LowSupportFiber G 0).card := by
  apply congrArg Finset.card
  ext x
  simp only [sevenHighT0LowSupportFiber, orderFortyNineLowVertices,
    Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
  aesop

/-- Adjacency incidences between any two low support fibers are symmetric. -/
theorem sevenHighT0DirectedIncidence_comm
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj] (a b : Nat) :
    sevenHighT0DirectedIncidence G a b =
      sevenHighT0DirectedIncidence G b a := by
  classical
  simp only [sevenHighT0DirectedIncidence]
  rw [← Finset.card_sigma, ← Finset.card_sigma]
  apply Finset.card_bij (fun p _ => ⟨p.2, p.1⟩)
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_filter,
      SimpleGraph.mem_neighborFinset] at hp ⊢
    exact ⟨hp.2.2, G.adj_symm hp.2.1, hp.1⟩
  · intro p hp q hq hpq
    cases p
    cases q
    cases hpq
    rfl
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_filter,
      SimpleGraph.mem_neighborFinset] at hp
    refine ⟨⟨p.2, p.1⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_filter,
        SimpleGraph.mem_neighborFinset]
      exact ⟨hp.2.2, G.adj_symm hp.2.1, hp.1⟩
    · cases p
      rfl

/-- Sum of the pointwise `P = E + k` law over an arbitrary support fiber. -/
theorem sevenHigh_t0_sum_pairNeighborCount_eq_sum_lowEmpty_add
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (k : Nat) :
    (∑ y ∈ sevenHighT0LowSupportFiber G k,
      sevenHighT0PairNeighborCount G y) =
      (∑ y ∈ sevenHighT0LowSupportFiber G k,
        sevenHighT0LowEmptyNeighborCount G y) +
        k * (sevenHighT0LowSupportFiber G k).card := by
  have hpoint : ∀ y ∈ sevenHighT0LowSupportFiber G k,
      sevenHighT0PairNeighborCount G y =
        sevenHighT0LowEmptyNeighborCount G y + k := by
    intro y hy
    have hyDegree := degree_eq_seven_of_mem_lowSupportFiber
      G hfree hmin hy
    have hySupport := (Finset.mem_filter.mp hy).2
    have hlocal :=
      sevenHigh_t0_pairNeighborCount_eq_lowEmptyNeighborCount_add_support
        G hfree hmin hHigh hzero hyDegree
    simpa [sevenHighT0PairNeighborCount,
      sevenHighT0LowEmptyNeighborCount, hySupport] using hlocal
  calc
    (∑ y ∈ sevenHighT0LowSupportFiber G k,
        sevenHighT0PairNeighborCount G y) =
        ∑ y ∈ sevenHighT0LowSupportFiber G k,
          (sevenHighT0LowEmptyNeighborCount G y + k) := by
            apply Finset.sum_congr rfl
            intro y hy
            exact hpoint y hy
    _ = (∑ y ∈ sevenHighT0LowSupportFiber G k,
          sevenHighT0LowEmptyNeighborCount G y) +
          k * (sevenHighT0LowSupportFiber G k).card := by
            rw [Finset.sum_add_distrib]
            simp [Nat.mul_comm]

/-- Pair-support roots contribute the constant `2 · 21 = 42`. -/
theorem sevenHigh_t0_pairFiber_global_balance
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0) :
    (∑ y ∈ sevenHighT0LowSupportFiber G 2,
      sevenHighT0PairNeighborCount G y) =
      (∑ y ∈ sevenHighT0LowSupportFiber G 2,
        sevenHighT0LowEmptyNeighborCount G y) + 42 := by
  have hcensus := sevenHigh_t0_global_incidence G hfree hmin hHigh hzero
  have hcard : (sevenHighT0LowSupportFiber G 2).card = 21 := by
    simpa [sevenHighT0LowSupportFiber, orderFortyNineHighSupport,
      orderFortyNineHighIncidenceCount] using hcensus.2.2
  have hsum := sevenHigh_t0_sum_pairNeighborCount_eq_sum_lowEmpty_add
    G hfree hmin hHigh hzero 2
  rw [hcard] at hsum
  norm_num at hsum ⊢
  exact hsum

/-- Singleton-support roots contribute the constant `1 · 14 = 14`. -/
theorem sevenHigh_t0_singletonFiber_global_balance
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0) :
    (∑ y ∈ sevenHighT0LowSupportFiber G 1,
      sevenHighT0PairNeighborCount G y) =
      (∑ y ∈ sevenHighT0LowSupportFiber G 1,
        sevenHighT0LowEmptyNeighborCount G y) + 14 := by
  have hcensus := sevenHigh_t0_global_incidence G hfree hmin hHigh hzero
  have hcard : (sevenHighT0LowSupportFiber G 1).card = 14 := by
    simpa [sevenHighT0LowSupportFiber, orderFortyNineHighSupport,
      orderFortyNineHighIncidenceCount] using hcensus.2.1
  have hsum := sevenHigh_t0_sum_pairNeighborCount_eq_sum_lowEmpty_add
    G hfree hmin hHigh hzero 1
  rw [hcard] at hsum
  norm_num at hsum ⊢
  exact hsum

/-- Empty-support roots have equal aggregate pair and low-empty counts. -/
theorem sevenHigh_t0_emptyFiber_global_balance
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0) :
    (∑ y ∈ sevenHighT0LowSupportFiber G 0,
      sevenHighT0PairNeighborCount G y) =
      ∑ y ∈ sevenHighT0LowSupportFiber G 0,
        sevenHighT0LowEmptyNeighborCount G y := by
  have hsum := sevenHigh_t0_sum_pairNeighborCount_eq_sum_lowEmpty_add
    G hfree hmin hHigh hzero 0
  simpa using hsum

/-- The three graph sums, rewritten as directed inter-fiber incidences and
oriented with pair fibers on the left.  These are the exact pre-edge-count
forms of the quotient pair/singleton/empty balance equations. -/
theorem sevenHigh_t0_directedIncidence_global_balances
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0) :
    sevenHighT0DirectedIncidence G 2 2 =
        sevenHighT0DirectedIncidence G 0 2 + 42 ∧
      sevenHighT0DirectedIncidence G 2 1 =
        sevenHighT0DirectedIncidence G 0 1 + 14 ∧
      sevenHighT0DirectedIncidence G 2 0 =
        sevenHighT0DirectedIncidence G 0 0 := by
  have hpair := sevenHigh_t0_pairFiber_global_balance
    G hfree hmin hHigh hzero
  have hsingleton := sevenHigh_t0_singletonFiber_global_balance
    G hfree hmin hHigh hzero
  have hempty := sevenHigh_t0_emptyFiber_global_balance
    G hfree hmin hHigh hzero
  simp_rw [pairNeighborCount_eq_fiberIncidence G hfree hmin,
    lowEmptyNeighborCount_eq_fiberIncidence] at hpair hsingleton hempty
  change sevenHighT0DirectedIncidence G 2 2 =
    sevenHighT0DirectedIncidence G 2 0 + 42 at hpair
  change sevenHighT0DirectedIncidence G 1 2 =
    sevenHighT0DirectedIncidence G 1 0 + 14 at hsingleton
  change sevenHighT0DirectedIncidence G 0 2 =
    sevenHighT0DirectedIncidence G 0 0 at hempty
  rw [sevenHighT0DirectedIncidence_comm G 2 0] at hpair
  rw [sevenHighT0DirectedIncidence_comm G 1 2,
    sevenHighT0DirectedIncidence_comm G 1 0] at hsingleton
  rw [sevenHighT0DirectedIncidence_comm G 0 2] at hempty
  exact ⟨hpair, hsingleton, hempty⟩

/-- Summing the graph-local empty-neighbor capacities over the three low
support fibers gives the global directed bounds used by the quotient model. -/
theorem sevenHigh_t0_directedIncidence_empty_capacity_bounds
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0) :
    sevenHighT0DirectedIncidence G 2 0 ≤ 21 ∧
      sevenHighT0DirectedIncidence G 1 0 ≤ 28 ∧
      sevenHighT0DirectedIncidence G 0 0 ≤ 21 := by
  have hcensus := sevenHigh_t0_global_incidence G hfree hmin hHigh hzero
  have hcardTwo : (sevenHighT0LowSupportFiber G 2).card = 21 := by
    simpa [sevenHighT0LowSupportFiber, orderFortyNineHighSupport,
      orderFortyNineHighIncidenceCount] using hcensus.2.2
  have hcardOne : (sevenHighT0LowSupportFiber G 1).card = 14 := by
    simpa [sevenHighT0LowSupportFiber, orderFortyNineHighSupport,
      orderFortyNineHighIncidenceCount] using hcensus.2.1
  have hcardZero : (sevenHighT0LowSupportFiber G 0).card = 7 := by
    simpa [sevenHighT0LowSupportFiber, orderFortyNineHighSupport,
      orderFortyNineHighIncidenceCount] using hcensus.1
  have htwo : (∑ y ∈ sevenHighT0LowSupportFiber G 2,
      sevenHighT0LowEmptyNeighborCount G y) ≤
      ∑ _y ∈ sevenHighT0LowSupportFiber G 2, 1 := by
    apply Finset.sum_le_sum
    intro y hy
    exact sevenHigh_t0_pairRoot_lowEmptyNeighbor_bound
      G hfree hmin hHigh hzero
        (degree_eq_seven_of_mem_lowSupportFiber G hfree hmin hy)
        (Finset.mem_filter.mp hy).2
  have hone : (∑ y ∈ sevenHighT0LowSupportFiber G 1,
      sevenHighT0LowEmptyNeighborCount G y) ≤
      ∑ _y ∈ sevenHighT0LowSupportFiber G 1, 2 := by
    apply Finset.sum_le_sum
    intro y hy
    exact sevenHigh_t0_singletonRoot_lowEmptyNeighbor_bound
      G hfree hmin hHigh hzero
        (degree_eq_seven_of_mem_lowSupportFiber G hfree hmin hy)
        (Finset.mem_filter.mp hy).2
  have hzeroFiber : (∑ y ∈ sevenHighT0LowSupportFiber G 0,
      sevenHighT0LowEmptyNeighborCount G y) ≤
      ∑ _y ∈ sevenHighT0LowSupportFiber G 0, 3 := by
    apply Finset.sum_le_sum
    intro y hy
    exact sevenHigh_t0_emptyRoot_lowEmptyNeighbor_bound
      G hfree hmin hHigh hzero
        (degree_eq_seven_of_mem_lowSupportFiber G hfree hmin hy)
  simp_rw [lowEmptyNeighborCount_eq_fiberIncidence] at htwo hone hzeroFiber
  change sevenHighT0DirectedIncidence G 2 0 ≤ _ at htwo
  change sevenHighT0DirectedIncidence G 1 0 ≤ _ at hone
  change sevenHighT0DirectedIncidence G 0 0 ≤ _ at hzeroFiber
  simp [hcardTwo] at htwo
  simp [hcardOne] at hone
  simp [hcardZero] at hzeroFiber
  exact ⟨htwo, hone, hzeroFiber⟩

end

end Erdos85

#print axioms Erdos85.sevenHigh_t0_sum_pairNeighborCount_eq_sum_lowEmpty_add
#print axioms Erdos85.sevenHigh_t0_pairFiber_global_balance
#print axioms Erdos85.sevenHigh_t0_singletonFiber_global_balance
#print axioms Erdos85.sevenHigh_t0_emptyFiber_global_balance
#print axioms Erdos85.sevenHighT0DirectedIncidence_comm
#print axioms Erdos85.sevenHigh_t0_directedIncidence_global_balances
#print axioms Erdos85.sevenHigh_t0_directedIncidence_empty_capacity_bounds
