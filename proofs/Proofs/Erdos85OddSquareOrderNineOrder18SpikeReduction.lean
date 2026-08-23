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
#print axioms Erdos85.orderNine_order18_highSpike_highRoot_neighbors_subset_lowSet
#print axioms Erdos85.orderNine_order18_highSpike_highRoot_equation_of_defect_transfer
#print axioms Erdos85.orderNine_order18_lowSpike_highRoot_equation_of_defect_transfer
#print axioms Erdos85.false_of_orderNine_order18_highSpike_three_partners
#print axioms Erdos85.orderNine_order18_lowSpike_center_eq_owner_of_partner_bounds

end

end Erdos85
