import Proofs.Erdos85OddSquareOrderNineArticulationLowSetTransfer

/-!
# The order-eighteen excess-two spike reduction

Node: B.3 / symmetric `(18,59)` articulation branch, audit equations
(29)--(32).

This file isolates the finite terminal after the excess-two defect-transfer
calculation.  There are three distinct bin-one partners of the bin-three
owner.  In the high-spike profile they all lie in the low set, contradicting
the owner low-set cap.  In the low-spike profile, equation (32) caps the
owner's low-set degree by one; the high-root transfer gives at least three
low-set partners when the spike center is bin zero and at least two when it
is bin one.  Hence the spike center must be the owner.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 2000000

/-- The integer square-sum refinement behind audit (29).  A bounded
ordinary incidence profile with total `516` and square total `3434` is
obtained from the balanced `6/7` profile by moving one unit either down or
up. -/
theorem orderNine_order18_excessTwo_incidence_count_classification
    (n₀ n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈ n₉ : ℕ)
    (hcount : n₀ + n₁ + n₂ + n₃ + n₄ + n₅ + n₆ + n₇ + n₈ + n₉ = 78)
    (hsum : n₁ + 2 * n₂ + 3 * n₃ + 4 * n₄ + 5 * n₅ + 6 * n₆ +
      7 * n₇ + 8 * n₈ + 9 * n₉ = 516)
    (hsquare : n₁ + 4 * n₂ + 9 * n₃ + 16 * n₄ + 25 * n₅ + 36 * n₆ +
      49 * n₇ + 64 * n₈ + 81 * n₉ = 3434) :
    (n₀ = 0 ∧ n₁ = 0 ∧ n₂ = 0 ∧ n₃ = 0 ∧ n₄ = 0 ∧
      n₅ = 1 ∧ n₆ = 28 ∧ n₇ = 49 ∧ n₈ = 0 ∧ n₉ = 0) ∨
    (n₀ = 0 ∧ n₁ = 0 ∧ n₂ = 0 ∧ n₃ = 0 ∧ n₄ = 0 ∧
      n₅ = 0 ∧ n₆ = 31 ∧ n₇ = 46 ∧ n₈ = 1 ∧ n₉ = 0) := by
  have hexcess :
      42 * n₀ + 30 * n₁ + 20 * n₂ + 12 * n₃ + 6 * n₄ +
        2 * n₅ + 2 * n₈ + 6 * n₉ = 2 := by
    omega
  have hn₀ : n₀ = 0 := by omega
  have hn₁ : n₁ = 0 := by omega
  have hn₂ : n₂ = 0 := by omega
  have hn₃ : n₃ = 0 := by omega
  have hn₄ : n₄ = 0 := by omega
  have hn₉ : n₉ = 0 := by omega
  have hspike : (n₅ = 1 ∧ n₈ = 0) ∨ (n₅ = 0 ∧ n₈ = 1) := by
    omega
  rcases hspike with ⟨hn₅, hn₈⟩ | ⟨hn₅, hn₈⟩
  · left
    omega
  · right
    omega

/-- The graph-facing moment package for the symmetric order-eighteen cut.
Here `R` is the sixty-point ordinary complement `O \ S` (so it includes the
deleted owner), each high root has eight neighbors in `R`, and the oriented
defect boundary has size two.  The exact cut identity gives the incidence
sum `516` and square sum `3434` used by the arithmetic classifier above. -/
theorem orderNine_order18_largeOrdinaryShore_incidence_moments
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hcard : Fintype.card V = 81)
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃)
    (h₂₃ : h₂ ≠ h₃) (R : Finset V)
    (hRH : Disjoint R {h₁, h₂, h₃})
    (hRcard : R.card = 60)
    (hhigh₁ : (G.neighborFinset h₁ ∩ R).card = 8)
    (hhigh₂ : (G.neighborFinset h₂ ∩ R).card = 8)
    (hhigh₃ : (G.neighborFinset h₃ ∩ R).card = 8)
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ h ∈ ({h₁, h₂, h₃} : Finset V), G.degree h = 10)
    (hboundary : (∑ x ∈ R,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ R)).card) = 2) :
    let O := (Finset.univ : Finset V) \ {h₁, h₂, h₃}
    let f := fun x : ↥(↑O : Set V) ↦ (G.neighborFinset x.1 ∩ R).card
    Fintype.card ↥(↑O : Set V) = 78 ∧
      (∑ x, f x) = 516 ∧ (∑ x, (f x) ^ 2) = 3434 := by
  classical
  let H : Finset V := {h₁, h₂, h₃}
  let O := (Finset.univ : Finset V) \ H
  let f := fun x : ↥(↑O : Set V) ↦ (G.neighborFinset x.1 ∩ R).card
  have hHcard : H.card = 3 := by simp [H, h₁₂, h₁₃, h₂₃]
  have hOcard : Fintype.card ↥(↑O : Set V) = 78 := by
    rw [Set.fintypeCard_eq_ncard, Set.ncard_coe_finset]
    dsimp [O]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ H), Finset.card_univ,
      hcard, hHcard]
  have hsumRaw := orderNine_ordinary_neighbor_inter_sum
    G H R hRH hdegOrd
  have hsum : (∑ x, f x) = 516 := by
    dsimp only [f, O]
    dsimp only at hsumRaw
    rw [hRcard] at hsumRaw
    simp [H, h₁₂, h₁₃, h₂₃, hhigh₁, hhigh₂, hhigh₃] at hsumRaw
    exact hsumRaw
  have hprodRaw := orderNine_cut_ordinary_high_product_identity
    G hfree hcard H R hdegOrd hdegHigh 2 hboundary
  have hhighProd : (∑ h ∈ H, (G.neighborFinset h ∩ R).card *
      (10 - (G.neighborFinset h ∩ R).card)) = 48 := by
    simp [H, h₁₂, h₁₃, h₂₃, hhigh₁, hhigh₂, hhigh₃]
  have hprod : (∑ x, f x * (9 - f x)) = 1210 := by
    dsimp only [f, O]
    dsimp only at hprodRaw
    rw [hhighProd, hRcard] at hprodRaw
    norm_num at hprodRaw
    omega
  have hfle : ∀ x, f x ≤ 9 := by
    intro x
    have hle := Finset.card_le_card (Finset.inter_subset_left :
      G.neighborFinset x.1 ∩ R ⊆ G.neighborFinset x.1)
    rw [G.card_neighborFinset_eq_degree,
      hdegOrd x.1 (Finset.mem_sdiff.mp x.2).2] at hle
    exact hle
  have hpoint : ∀ x, (f x) ^ 2 + f x * (9 - f x) = 9 * f x := by
    intro x
    have hmul : f x * f x ≤ f x * 9 := Nat.mul_le_mul_left (f x) (hfle x)
    rw [pow_two, Nat.mul_sub_left_distrib]
    simpa [mul_comm] using Nat.add_sub_of_le hmul
  have hsumsqAdd : (∑ x, (f x) ^ 2) + ∑ x, f x * (9 - f x) =
      9 * ∑ x, f x := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ x, ((f x) ^ 2 + f x * (9 - f x))) = ∑ x, 9 * f x := by
        apply Finset.sum_congr rfl
        intro x _
        exact hpoint x
      _ = 9 * ∑ x, f x := by rw [Finset.mul_sum]
  refine ⟨hOcard, hsum, ?_⟩
  rw [hprod, hsum] at hsumsqAdd
  have hs := congrArg (fun n : ℕ => n - 1210) hsumsqAdd
  norm_num at hs
  exact hs

/-- Histogram-facing form of the excess-two classification.  This generic
adapter turns the three raw moments of any `0..9`-valued function on 78
points into the two exact profiles, so the graph layer need not manipulate
ten fiber counts by hand. -/
theorem orderNine_order18_excessTwo_function_profile
    {X : Type*} [Fintype X] [DecidableEq X]
    (f : X → ℕ) (hcard : Fintype.card X = 78)
    (hbound : ∀ x, f x ≤ 9)
    (hsum : ∑ x, f x = 516)
    (hsquare : ∑ x, (f x) ^ 2 = 3434) :
    let n := fun i : ℕ ↦ ((Finset.univ : Finset X).filter fun x ↦ f x = i).card
    (n 0 = 0 ∧ n 1 = 0 ∧ n 2 = 0 ∧ n 3 = 0 ∧ n 4 = 0 ∧
      n 5 = 1 ∧ n 6 = 28 ∧ n 7 = 49 ∧ n 8 = 0 ∧ n 9 = 0) ∨
    (n 0 = 0 ∧ n 1 = 0 ∧ n 2 = 0 ∧ n 3 = 0 ∧ n 4 = 0 ∧
      n 5 = 0 ∧ n 6 = 31 ∧ n 7 = 46 ∧ n 8 = 1 ∧ n 9 = 0) := by
  classical
  let n := fun i : ℕ ↦ ((Finset.univ : Finset X).filter fun x ↦ f x = i).card
  have hmaps : ((Finset.univ : Finset X) : Set X).MapsTo f (Finset.range 10) := by
    intro x _
    exact Finset.mem_range.mpr (by have := hbound x; omega)
  have hcountRaw := Finset.card_eq_sum_card_fiberwise hmaps
  have hcount : n 0 + n 1 + n 2 + n 3 + n 4 + n 5 + n 6 + n 7 + n 8 + n 9 = 78 := by
    rw [Finset.card_univ, hcard] at hcountRaw
    simpa [n, Finset.sum_range_succ] using hcountRaw.symm
  have hsumRaw := Finset.sum_fiberwise_of_maps_to hmaps f
  have hfiberSum : ∀ j : ℕ,
      (∑ x ∈ (Finset.univ : Finset X).filter (fun x ↦ f x = j), f x) =
        n j * j := by
    intro j
    exact Finset.sum_const_nat (fun x hx ↦ (Finset.mem_filter.mp hx).2)
  have hsumCounts : n 1 + 2 * n 2 + 3 * n 3 + 4 * n 4 + 5 * n 5 +
      6 * n 6 + 7 * n 7 + 8 * n 8 + 9 * n 9 = 516 := by
    rw [hsum] at hsumRaw
    simp only [Finset.sum_range_succ] at hsumRaw
    rw [hfiberSum 0, hfiberSum 1, hfiberSum 2, hfiberSum 3, hfiberSum 4,
      hfiberSum 5, hfiberSum 6, hfiberSum 7, hfiberSum 8, hfiberSum 9] at hsumRaw
    norm_num [mul_comm] at hsumRaw ⊢
    exact hsumRaw
  have hsquareRaw := Finset.sum_fiberwise_of_maps_to hmaps
    (fun x : X ↦ (f x) ^ 2)
  have hfiberSquare : ∀ j : ℕ,
      (∑ x ∈ (Finset.univ : Finset X).filter (fun x ↦ f x = j), (f x) ^ 2) =
        n j * j ^ 2 := by
    intro j
    exact Finset.sum_const_nat (fun x hx ↦ congrArg (· ^ 2) (Finset.mem_filter.mp hx).2)
  have hsquareCounts : n 1 + 4 * n 2 + 9 * n 3 + 16 * n 4 + 25 * n 5 +
      36 * n 6 + 49 * n 7 + 64 * n 8 + 81 * n 9 = 3434 := by
    rw [hsquare] at hsquareRaw
    simp only [Finset.sum_range_succ] at hsquareRaw
    rw [hfiberSquare 0, hfiberSquare 1, hfiberSquare 2, hfiberSquare 3,
      hfiberSquare 4, hfiberSquare 5, hfiberSquare 6, hfiberSquare 7,
      hfiberSquare 8, hfiberSquare 9] at hsquareRaw
    norm_num [mul_comm] at hsquareRaw ⊢
    exact hsquareRaw
  exact orderNine_order18_excessTwo_incidence_count_classification
    (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) (n 9)
      hcount hsumCounts hsquareCounts

/-- Direct graph-facing form of audit (29): the symmetric sixty-point
ordinary shore has exactly the low-spike or high-spike incidence histogram. -/
theorem orderNine_order18_largeOrdinaryShore_incidence_profile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hcard : Fintype.card V = 81)
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃)
    (h₂₃ : h₂ ≠ h₃) (R : Finset V)
    (hRH : Disjoint R {h₁, h₂, h₃})
    (hRcard : R.card = 60)
    (hhigh₁ : (G.neighborFinset h₁ ∩ R).card = 8)
    (hhigh₂ : (G.neighborFinset h₂ ∩ R).card = 8)
    (hhigh₃ : (G.neighborFinset h₃ ∩ R).card = 8)
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ h ∈ ({h₁, h₂, h₃} : Finset V), G.degree h = 10)
    (hboundary : (∑ x ∈ R,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ R)).card) = 2) :
    let O := (Finset.univ : Finset V) \ {h₁, h₂, h₃}
    let f := fun x : ↥(↑O : Set V) ↦ (G.neighborFinset x.1 ∩ R).card
    let n := fun i : ℕ ↦ ((Finset.univ : Finset ↥(↑O : Set V)).filter
      fun x ↦ f x = i).card
    (n 0 = 0 ∧ n 1 = 0 ∧ n 2 = 0 ∧ n 3 = 0 ∧ n 4 = 0 ∧
      n 5 = 1 ∧ n 6 = 28 ∧ n 7 = 49 ∧ n 8 = 0 ∧ n 9 = 0) ∨
    (n 0 = 0 ∧ n 1 = 0 ∧ n 2 = 0 ∧ n 3 = 0 ∧ n 4 = 0 ∧
      n 5 = 0 ∧ n 6 = 31 ∧ n 7 = 46 ∧ n 8 = 1 ∧ n 9 = 0) := by
  classical
  let H : Finset V := {h₁, h₂, h₃}
  let O := (Finset.univ : Finset V) \ H
  let f := fun x : ↥(↑O : Set V) ↦ (G.neighborFinset x.1 ∩ R).card
  have hmoments := orderNine_order18_largeOrdinaryShore_incidence_moments
    G hfree hcard h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ R hRH hRcard
      hhigh₁ hhigh₂ hhigh₃ hdegOrd hdegHigh hboundary
  change Fintype.card ↥(↑O : Set V) = 78 ∧
      (∑ x, f x) = 516 ∧ (∑ x, (f x) ^ 2) = 3434 at hmoments
  have hbound : ∀ x, f x ≤ 9 := by
    intro x
    have hle := Finset.card_le_card (Finset.inter_subset_left :
      G.neighborFinset x.1 ∩ R ⊆ G.neighborFinset x.1)
    rw [G.card_neighborFinset_eq_degree,
      hdegOrd x.1 (Finset.mem_sdiff.mp x.2).2] at hle
    exact hle
  exact orderNine_order18_excessTwo_function_profile f hmoments.1 hbound
    hmoments.2.1 hmoments.2.2

/-- Evaluation of the high-spike form of audit equation (31) at a high
root.  Defect-high isolation makes the left side zero, while the high root
lies in neither ordinary shore. -/
theorem orderNine_order18_highSpike_highRoot_equation_of_defect_transfer
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (S H Z : Finset V) (c h : V)
    (hhH : h ∈ H) (hhS : h ∉ S)
    (hDzero : (D.neighborFinset h ∩ S).card = 0)
    (heq31 : ∀ v : V,
      ((D.neighborFinset v ∩ S).card : ℤ) =
        8 * (if v ∈ S then 1 else 0) + 3 +
          7 * (if v ∈ H then 1 else 0) -
          ((G.neighborFinset v ∩ Z).card : ℤ) +
          (if G.Adj v c then 1 else 0)) :
    (G.neighborFinset h ∩ Z).card =
      10 + if G.Adj h c then 1 else 0 := by
  have heq := heq31 h
  rw [hDzero] at heq
  simp only [Nat.cast_zero, if_neg hhS, if_pos hhH] at heq
  by_cases hadj : G.Adj h c <;> simp [hadj] at heq ⊢ <;> omega

/-- Evaluation of the low-spike form of (31) at a high root.  It is best
kept as `Z`-degree plus the spike incidence equals ten: each high root can
lose at most the one slot charged to `c`. -/
theorem orderNine_order18_lowSpike_highRoot_equation_of_defect_transfer
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (S H Z : Finset V) (c h : V)
    (hhH : h ∈ H) (hhS : h ∉ S)
    (hDzero : (D.neighborFinset h ∩ S).card = 0)
    (heq31 : ∀ v : V,
      ((D.neighborFinset v ∩ S).card : ℤ) =
        8 * (if v ∈ S then 1 else 0) + 3 +
          7 * (if v ∈ H then 1 else 0) -
          ((G.neighborFinset v ∩ Z).card : ℤ) -
          (if G.Adj v c then 1 else 0)) :
    (G.neighborFinset h ∩ Z).card +
      (if G.Adj h c then 1 else 0) = 10 := by
  have heq := heq31 h
  rw [hDzero] at heq
  simp only [Nat.cast_zero, if_neg hhS, if_pos hhH] at heq
  by_cases hadj : G.Adj h c <;> simp [hadj] at heq ⊢ <;> omega

/-- The high-spike high-root equation forces the spike center to be
high-free.  In cardinal form, equation (31) at a degree-ten high root says
that its `Z`-degree is `10 + 1_[h~c]`; the degree bound leaves no room for
the extra point. -/
theorem orderNine_order18_highSpike_center_not_adjacent_highRoot
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z : Finset V) {h c : V}
    (hdeg : G.degree h = 10)
    (heq : (G.neighborFinset h ∩ Z).card =
      10 + if G.Adj h c then 1 else 0) :
    ¬ G.Adj h c := by
  intro hadj
  have hle : (G.neighborFinset h ∩ Z).card ≤ G.degree h := by
    simpa [G.card_neighborFinset_eq_degree] using
      Finset.card_le_card (Finset.inter_subset_left :
        G.neighborFinset h ∩ Z ⊆ G.neighborFinset h)
  rw [heq, if_pos hadj, hdeg] at hle
  omega

/-- Once the high-spike center is excluded from a high root, the same
high-root equation says that all ten neighbors of the root lie in `Z`. -/
theorem orderNine_order18_highSpike_highRoot_neighbors_subset_lowSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z : Finset V) {h c : V}
    (hdeg : G.degree h = 10)
    (heq : (G.neighborFinset h ∩ Z).card =
      10 + if G.Adj h c then 1 else 0) :
    G.neighborFinset h ⊆ Z := by
  have hnadj := orderNine_order18_highSpike_center_not_adjacent_highRoot
    G Z hdeg heq
  have hcard : (G.neighborFinset h ∩ Z).card =
      (G.neighborFinset h).card := by
    rw [heq, if_neg hnadj, G.card_neighborFinset_eq_degree, hdeg]
  exact Finset.inter_eq_left.mp (Finset.eq_of_subset_of_card_le
    Finset.inter_subset_left (by omega :
      (G.neighborFinset h).card ≤ (G.neighborFinset h ∩ Z).card))

/-- **High-spike terminal.**  Three distinct owner partners cannot all lie
in a low set containing at most two owner-neighbors. -/
theorem false_of_orderNine_order18_highSpike_three_partners
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (owner : V) (K Z : Finset V)
    (hKcard : K.card = 3)
    (hKowner : K ⊆ G.neighborFinset owner)
    (hKZ : K ⊆ Z)
    (hownerZ : (G.neighborFinset owner ∩ Z).card ≤ 2) :
    False := by
  have hsub : K ⊆ G.neighborFinset owner ∩ Z := by
    intro y hy
    exact Finset.mem_inter.mpr ⟨hKowner hy, hKZ hy⟩
  have := Finset.card_le_card hsub
  omega

/-- Equation (32) always bounds the owner's low-set degree by one. -/
theorem orderNine_order18_lowSpike_owner_lowSet_degree_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (owner c : V) (Z : Finset V)
    (heq32 : (G.neighborFinset owner ∩ Z).card =
      if G.Adj owner c then 0 else 1) :
    (G.neighborFinset owner ∩ Z).card ≤ 1 := by
  split at heq32 <;> omega

/-- **Low-spike reduction.**  Let `K` be the three distinct bin-one
partners of the owner.  The high-root form of (31) supplies all three of
them in `Z` when the spike center is bin zero, and at least two when it is
bin one.  Equation (32) permits at most one.  Thus, among the exhaustive
possibilities `c=owner`, `c∈B₀`, and `c∈B₁`, only `c=owner` remains.

The two partner hypotheses are deliberately stated as the exact finite-set
outputs needed from the forthcoming graph-facing transfer wrapper. -/
theorem orderNine_order18_lowSpike_center_eq_owner_of_partner_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (owner c : V) (K Z B₀ B₁ : Finset V)
    (hKcard : K.card = 3)
    (hKowner : K ⊆ G.neighborFinset owner)
    (hcases : c = owner ∨ c ∈ B₀ ∨ c ∈ B₁)
    (hbinZero : c ∈ B₀ → K ⊆ Z)
    (hbinOne : c ∈ B₁ → 2 ≤ (K ∩ Z).card)
    (heq32 : (G.neighborFinset owner ∩ Z).card =
      if G.Adj owner c then 0 else 1) :
    c = owner := by
  have hownerZ : (G.neighborFinset owner ∩ Z).card ≤ 1 :=
    orderNine_order18_lowSpike_owner_lowSet_degree_le_one
      G owner c Z heq32
  rcases hcases with rfl | hc0 | hc1
  · rfl
  · have hsub : K ⊆ G.neighborFinset owner ∩ Z := by
      intro y hy
      exact Finset.mem_inter.mpr ⟨hKowner hy, hbinZero hc0 hy⟩
    have hle := Finset.card_le_card hsub
    omega
  · have hsub : K ∩ Z ⊆ G.neighborFinset owner ∩ Z := by
      intro y hy
      exact Finset.mem_inter.mpr ⟨hKowner (Finset.mem_inter.mp hy).1,
        (Finset.mem_inter.mp hy).2⟩
    have hle := Finset.card_le_card hsub
    have htwo := hbinOne hc1
    omega

#print axioms Erdos85.orderNine_order18_highSpike_center_not_adjacent_highRoot
#print axioms Erdos85.orderNine_order18_excessTwo_incidence_count_classification
#print axioms Erdos85.orderNine_order18_largeOrdinaryShore_incidence_moments
#print axioms Erdos85.orderNine_order18_excessTwo_function_profile
#print axioms Erdos85.orderNine_order18_largeOrdinaryShore_incidence_profile
#print axioms Erdos85.orderNine_order18_highSpike_highRoot_neighbors_subset_lowSet
#print axioms Erdos85.orderNine_order18_highSpike_highRoot_equation_of_defect_transfer
#print axioms Erdos85.orderNine_order18_lowSpike_highRoot_equation_of_defect_transfer
#print axioms Erdos85.false_of_orderNine_order18_highSpike_three_partners
#print axioms Erdos85.orderNine_order18_lowSpike_center_eq_owner_of_partner_bounds

end

end Erdos85
