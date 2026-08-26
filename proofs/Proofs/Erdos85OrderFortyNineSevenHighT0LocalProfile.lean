import Proofs.Erdos85OrderFortyNineSevenHighT0LocalQuotientCapacity

/-!
# Pointwise P/S/E profiles in the seven-high empty-triple case

The high-support weights on a low neighborhood lie in `{0,1,2}` and sum to
seven.  Hence `2·P + S = 7` for the actual pair- and singleton-support
neighbor filters.  Combining this with the graph theorem `P = E + k` gives
the exact low-neighbor profiles `2E+S = 3,5,7` for pair-, singleton-, and
empty-support roots.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- A finite sum of `{0,1,2}`-valued weights is twice the two-fiber plus the
one-fiber. -/
theorem sum_eq_two_mul_card_eq_two_add_card_eq_one
    {α : Type*} [DecidableEq α]
    (S : Finset α) (weight : α → Nat)
    (hle : ∀ x ∈ S, weight x ≤ 2) :
    (∑ x ∈ S, weight x) =
      2 * (S.filter fun x => weight x = 2).card +
        (S.filter fun x => weight x = 1).card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      have haLe : weight a ≤ 2 := hle a (Finset.mem_insert_self _ _)
      have htail : ∀ x ∈ S, weight x ≤ 2 := by
        intro x hx
        exact hle x (Finset.mem_insert_of_mem hx)
      have hrec := ih htail
      rcases Nat.eq_zero_or_pos (weight a) with hzero | hpos
      · simp [Finset.filter_insert, ha, hzero]
        omega
      · have honeOrTwo : weight a = 1 ∨ weight a = 2 := by omega
        rcases honeOrTwo with hone | htwo
        · simp [Finset.filter_insert, ha, hone]
          omega
        · simp [Finset.filter_insert, ha, htwo]
          omega

private theorem sevenHigh_t0_neighbor_support_card_le_two
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    {y x : Fin 49} (_hxy : x ∈ G.neighborFinset y) :
    (orderFortyNineHighSupport G x).card ≤ 2 := by
  rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin (Fintype.card_fin 49) x with hx7 | hx8
  · have hle3 := orderFortyNine_highNeighborCount_le_three
        G hfree hmin (Fintype.card_fin 49) hx7
    change (orderFortyNineHighSupport G x).card ≤ 3 at hle3
    have hne3 : (orderFortyNineHighSupport G x).card ≠ 3 := by
      intro hx3
      have hxLow : x ∈ orderFortyNineLowVertices G := by
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_univ x, ?_⟩
        intro hxHigh
        have := (Finset.mem_filter.mp hxHigh).2
        omega
      have hxGlobal : x ∈ (orderFortyNineLowVertices G).filter fun z =>
          (G.neighborFinset z ∩ orderFortyNineHighVertices G).card = 3 := by
        exact Finset.mem_filter.mpr ⟨hxLow, by
          simpa [orderFortyNineHighSupport] using hx3⟩
      have hempty := Finset.card_eq_zero.mp hzero
      rw [hempty] at hxGlobal
      simp at hxGlobal
    omega
  · have hxHigh : x ∈ orderFortyNineHighVertices G := by
      simp [orderFortyNineHighVertices, hx8]
    have hxZero := orderFortyNine_highNeighborCount_eq_zero_of_high
      G hfree hmin (Fintype.card_fin 49) hxHigh
    change (orderFortyNineHighSupport G x).card = 0 at hxZero
    omega

/-- Actual-filter high-support profile around every low root. -/
theorem sevenHigh_t0_two_mul_pairNeighborCount_add_singletonNeighborCount_eq_seven
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    {y : Fin 49} (hy : G.degree y = 7) :
    2 * ((G.neighborFinset y).filter fun x =>
      (orderFortyNineHighSupport G x).card = 2).card +
      ((G.neighborFinset y).filter fun x =>
        (orderFortyNineHighSupport G x).card = 1).card = 7 := by
  have hprofile := sum_eq_two_mul_card_eq_two_add_card_eq_one
    (G.neighborFinset y) (fun x => (orderFortyNineHighSupport G x).card)
    (fun _ hx => sevenHigh_t0_neighbor_support_card_le_two
      G hfree hmin hzero hx)
  rw [sevenHigh_t0_sum_support_card_over_lowNeighborhood_eq_seven
    G hfree hmin hHigh hy] at hprofile
  exact hprofile.symm

private theorem sevenHigh_t0_lowEmpty_profile_of_support_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    {y : Fin 49} (hy : G.degree y = 7) {k rhs : Nat}
    (hySupport : (orderFortyNineHighSupport G y).card = k)
    (hrhs : 7 = 2 * k + rhs) :
    2 * ((((G.neighborFinset y).filter fun x =>
      (orderFortyNineHighSupport G x).card = 0).filter fun x =>
        x ∉ orderFortyNineHighVertices G).card) +
      ((G.neighborFinset y).filter fun x =>
        (orderFortyNineHighSupport G x).card = 1).card = rhs := by
  have hquotient :=
    sevenHigh_t0_pairNeighborCount_eq_lowEmptyNeighborCount_add_support
      G hfree hmin hHigh hzero hy
  have hprofile :=
    sevenHigh_t0_two_mul_pairNeighborCount_add_singletonNeighborCount_eq_seven
      G hfree hmin hHigh hzero hy
  rw [hySupport] at hquotient
  omega

/-- Pair-support root profile: `2E + S = 3`. -/
theorem sevenHigh_t0_pairRoot_lowEmpty_singleton_profile
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    {y : Fin 49} (hy : G.degree y = 7)
    (hySupport : (orderFortyNineHighSupport G y).card = 2) :
    2 * ((((G.neighborFinset y).filter fun x =>
      (orderFortyNineHighSupport G x).card = 0).filter fun x =>
        x ∉ orderFortyNineHighVertices G).card) +
      ((G.neighborFinset y).filter fun x =>
        (orderFortyNineHighSupport G x).card = 1).card = 3 := by
  exact sevenHigh_t0_lowEmpty_profile_of_support_card
    G hfree hmin hHigh hzero hy hySupport (by omega)

/-- Singleton-support root profile: `2E + S = 5`. -/
theorem sevenHigh_t0_singletonRoot_lowEmpty_singleton_profile
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    {y : Fin 49} (hy : G.degree y = 7)
    (hySupport : (orderFortyNineHighSupport G y).card = 1) :
    2 * ((((G.neighborFinset y).filter fun x =>
      (orderFortyNineHighSupport G x).card = 0).filter fun x =>
        x ∉ orderFortyNineHighVertices G).card) +
      ((G.neighborFinset y).filter fun x =>
        (orderFortyNineHighSupport G x).card = 1).card = 5 := by
  exact sevenHigh_t0_lowEmpty_profile_of_support_card
    G hfree hmin hHigh hzero hy hySupport (by omega)

/-- Empty-support root profile: `2E + S = 7`. -/
theorem sevenHigh_t0_emptyRoot_lowEmpty_singleton_profile
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    {y : Fin 49} (hy : G.degree y = 7)
    (hySupport : (orderFortyNineHighSupport G y).card = 0) :
    2 * ((((G.neighborFinset y).filter fun x =>
      (orderFortyNineHighSupport G x).card = 0).filter fun x =>
        x ∉ orderFortyNineHighVertices G).card) +
      ((G.neighborFinset y).filter fun x =>
        (orderFortyNineHighSupport G x).card = 1).card = 7 := by
  exact sevenHigh_t0_lowEmpty_profile_of_support_card
    G hfree hmin hHigh hzero hy hySupport (by omega)

end

end Erdos85

#print axioms Erdos85.sum_eq_two_mul_card_eq_two_add_card_eq_one
#print axioms Erdos85.sevenHigh_t0_two_mul_pairNeighborCount_add_singletonNeighborCount_eq_seven
#print axioms Erdos85.sevenHigh_t0_pairRoot_lowEmpty_singleton_profile
#print axioms Erdos85.sevenHigh_t0_singletonRoot_lowEmpty_singleton_profile
#print axioms Erdos85.sevenHigh_t0_emptyRoot_lowEmpty_singleton_profile
