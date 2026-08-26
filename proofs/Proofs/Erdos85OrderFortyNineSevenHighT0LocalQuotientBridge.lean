import Proofs.Erdos85OrderFortyNineSevenHighT0ActualSingletonCompatibility

/-!
# Graph-facing local quotient bridge for the seven-high empty-triple case

The quotient arithmetic is a pointwise consequence of a small general
counting identity: for weights in `{0,1,2}`, total weight plus the number of
zeros equals the number of points plus the number of twos.  Applied to the
seven neighbors of a low vertex, whose high-support weights sum to seven,
this says that the number of pair-support neighbors equals the number of
zero-support neighbors.  The latter includes the root's high neighbors; once
they are separated off this is exactly `P = E + k`.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Euler characteristic of a finite family of weights in `{0,1,2}`. -/
theorem sum_add_card_eq_zero_eq_card_add_card_eq_two
    {α : Type*} [DecidableEq α]
    (S : Finset α) (weight : α → Nat)
    (hle : ∀ x ∈ S, weight x ≤ 2) :
    (∑ x ∈ S, weight x) + (S.filter fun x => weight x = 0).card =
      S.card + (S.filter fun x => weight x = 2).card := by
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

/-- If the total of `{0,1,2}`-valued weights equals the number of points,
then the number of twos equals the number of zeros. -/
theorem card_eq_two_eq_card_eq_zero_of_sum_eq_card
    {α : Type*} [DecidableEq α]
    (S : Finset α) (weight : α → Nat)
    (hle : ∀ x ∈ S, weight x ≤ 2)
    (hsum : (∑ x ∈ S, weight x) = S.card) :
    (S.filter fun x => weight x = 2).card =
      (S.filter fun x => weight x = 0).card := by
  have h := sum_add_card_eq_zero_eq_card_add_card_eq_two S weight hle
  omega

/-- Graph-facing local quotient equation.  Around every low vertex in the
seven-high `t=0` stratum, pair-support graph neighbors and zero-support graph
neighbors occur equally often.  Zero-support here intentionally includes the
high neighbors; separating those `k` vertices gives the usual `P = E + k`.
-/
theorem sevenHigh_t0_pairNeighborCount_eq_zeroSupportNeighborCount
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    {y : Fin 49} (hy : G.degree y = 7) :
    ((G.neighborFinset y).filter fun x =>
      (orderFortyNineHighSupport G x).card = 2).card =
    ((G.neighborFinset y).filter fun x =>
      (orderFortyNineHighSupport G x).card = 0).card := by
  apply card_eq_two_eq_card_eq_zero_of_sum_eq_card
  · intro x hx
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
          exact (by
            have := (Finset.mem_filter.mp hxHigh).2
            omega)
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
      have hz := orderFortyNine_highNeighborCount_eq_zero_of_high
        G hfree hmin (Fintype.card_fin 49) hxHigh
      change (orderFortyNineHighSupport G x).card = 0 at hz
      omega
  · rw [sevenHigh_t0_sum_support_card_over_lowNeighborhood_eq_seven
      G hfree hmin hHigh hy]
    simp [SimpleGraph.card_neighborFinset_eq_degree, hy]

/-- Exact graph realization of the quotient law `P = E + k`.  The empty
count on the right is restricted to actual low vertices; the remaining
zero-support neighbors are precisely the `k` high neighbors of the root. -/
theorem sevenHigh_t0_pairNeighborCount_eq_lowEmptyNeighborCount_add_support
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    {y : Fin 49} (hy : G.degree y = 7) :
    ((G.neighborFinset y).filter fun x =>
      (orderFortyNineHighSupport G x).card = 2).card =
    (((G.neighborFinset y).filter fun x =>
      (orderFortyNineHighSupport G x).card = 0).filter fun x =>
        x ∉ orderFortyNineHighVertices G).card +
      (orderFortyNineHighSupport G y).card := by
  let Z := (G.neighborFinset y).filter fun x =>
    (orderFortyNineHighSupport G x).card = 0
  have hhighPart :
      (Z.filter fun x => x ∈ orderFortyNineHighVertices G) =
        orderFortyNineHighSupport G y := by
    ext x
    constructor
    · intro hx
      have hx' := Finset.mem_filter.mp hx
      have hxZ := Finset.mem_filter.mp hx'.1
      exact Finset.mem_inter.mpr ⟨hxZ.1, hx'.2⟩
    · intro hx
      have hx' := Finset.mem_inter.mp hx
      have hzeroX := orderFortyNine_highNeighborCount_eq_zero_of_high
        G hfree hmin (Fintype.card_fin 49) hx'.2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨hx'.1, ?_⟩, hx'.2⟩
      simpa [orderFortyNineHighSupport] using hzeroX
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Z) (p := fun x => x ∈ orderFortyNineHighVertices G)
  have hpair := sevenHigh_t0_pairNeighborCount_eq_zeroSupportNeighborCount
    G hfree hmin hHigh hzero hy
  change _ = (Z.filter fun x => x ∉ orderFortyNineHighVertices G).card + _
  change _ = Z.card at hpair
  rw [hpair, ← hsplit, hhighPart]
  omega

end

end Erdos85

#print axioms Erdos85.sum_add_card_eq_zero_eq_card_add_card_eq_two
#print axioms Erdos85.card_eq_two_eq_card_eq_zero_of_sum_eq_card
#print axioms Erdos85.sevenHigh_t0_pairNeighborCount_eq_zeroSupportNeighborCount
#print axioms Erdos85.sevenHigh_t0_pairNeighborCount_eq_lowEmptyNeighborCount_add_support
