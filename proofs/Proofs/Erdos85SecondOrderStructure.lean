import Proofs.Erdos85EvenAntipodalQuotient

/-!
# Structure at the second order above the Moore layer

At order `d(d-1)+3`, near-Moore regularity leaves exactly two units of
slack.  This module records the resulting parity trichotomy and uses the
odd branch to exclude this order outright.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Exact two-slack identity at order `d(d-1)+3`. -/
theorem card_external_add_degree_eq_two_add_localDegreeSum_of_secondOrder
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (x : V) :
    (externalRepairCandidates G x).card + d =
      2 + ∑ y : {z : V // z ∈ G.neighborSet x},
        (G.induce (G.neighborSet x)).degree y := by
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = e + 4 := ⟨d - 4, by omega⟩
    norm_num
    nlinarith
  have hreg : ∀ v : V, G.degree v = d :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by omega) hmin hbelow
  have hid := card_external_add_degree_sq_add_one_eq_card_add_localDegreeSum
    G hfree hreg x
  rw [hcard] at hid
  obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = e + 4 := ⟨d - 4, by omega⟩
  norm_num at hid ⊢
  nlinarith

/-- At the second order, there are at most two vertices beyond distance two,
and the local matching misses at most two incidences. -/
theorem secondOrder_external_le_two_and_localDegreeSum_large
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (x : V) :
    (externalRepairCandidates G x).card ≤ 2 ∧
      d - 2 ≤ ∑ y : {z : V // z ∈ G.neighborSet x},
        (G.induce (G.neighborSet x)).degree y := by
  have hid := card_external_add_degree_eq_two_add_localDegreeSum_of_secondOrder
    G hfree hd hmin hcard x
  have hlocal := sum_localNeighborhood_degrees_le_degree G hfree x
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = e + 4 := ⟨d - 4, by omega⟩
    norm_num
    nlinarith
  have hdeg := degree_eq_of_minDegree_card_lt_nextMooreLayer
    G hfree (by omega) hmin hbelow x
  rw [hdeg] at hlocal
  omega

/-- For odd degree, the two units split evenly: exactly one external vertex
and exactly one isolated vertex in each induced neighborhood. -/
theorem secondOrder_structure_of_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (hodd : Odd d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (x : V) :
    (externalRepairCandidates G x).card = 1 ∧
      (∑ y : {z : V // z ∈ G.neighborSet x},
        (G.induce (G.neighborSet x)).degree y) = d - 1 := by
  let S := ∑ y : {z : V // z ∈ G.neighborSet x},
    (G.induce (G.neighborSet x)).degree y
  have hid := card_external_add_degree_eq_two_add_localDegreeSum_of_secondOrder
    G hfree hd hmin hcard x
  have hb := secondOrder_external_le_two_and_localDegreeSum_large
    G hfree hd hmin hcard x
  have hSeven : Even S := by
    change Even (∑ y : {z : V // z ∈ G.neighborSet x},
      (G.induce (G.neighborSet x)).degree y)
    rw [(G.induce (G.neighborSet x)).sum_degrees_eq_twice_card_edges]
    exact even_two_mul _
  change (externalRepairCandidates G x).card + d = 2 + S at hid
  change (externalRepairCandidates G x).card ≤ 2 ∧ d - 2 ≤ S at hb
  change (externalRepairCandidates G x).card = 1 ∧ S = d - 1
  rw [Nat.odd_iff] at hodd
  rw [Nat.even_iff] at hSeven
  omega

/-- For even degree there are precisely two possibilities: no external
vertices and two missing local incidences, or two external vertices and a
perfect local matching. -/
theorem secondOrder_structure_of_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (x : V) :
    ((externalRepairCandidates G x).card = 0 ∧
      (∑ y : {z : V // z ∈ G.neighborSet x},
        (G.induce (G.neighborSet x)).degree y) = d - 2) ∨
    ((externalRepairCandidates G x).card = 2 ∧
      (∑ y : {z : V // z ∈ G.neighborSet x},
        (G.induce (G.neighborSet x)).degree y) = d) := by
  let S := ∑ y : {z : V // z ∈ G.neighborSet x},
    (G.induce (G.neighborSet x)).degree y
  have hid := card_external_add_degree_eq_two_add_localDegreeSum_of_secondOrder
    G hfree hd hmin hcard x
  have hb := secondOrder_external_le_two_and_localDegreeSum_large
    G hfree hd hmin hcard x
  have hSeven : Even S := by
    change Even (∑ y : {z : V // z ∈ G.neighborSet x},
      (G.induce (G.neighborSet x)).degree y)
    rw [(G.induce (G.neighborSet x)).sum_degrees_eq_twice_card_edges]
    exact even_two_mul _
  change (externalRepairCandidates G x).card + d = 2 + S at hid
  change (externalRepairCandidates G x).card ≤ 2 ∧ d - 2 ≤ S at hb
  change ((externalRepairCandidates G x).card = 0 ∧ S = d - 2) ∨
    ((externalRepairCandidates G x).card = 2 ∧ S = d)
  rw [Nat.even_iff] at heven hSeven
  omega

/-- In the odd second-order template, the beyond-distance-two relation is a
one-regular spanning graph. -/
theorem antipodalGraph_degree_eq_one_of_secondOrder_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (hodd : Odd d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (x : V) : (antipodalGraph G).degree x = 1 := by
  rw [← (antipodalGraph G).card_neighborFinset_eq_degree,
    antipodalGraph_neighborFinset, antipodalNeighbors, Finset.card_map]
  exact (secondOrder_structure_of_odd G hfree hd hodd hmin hcard x).1

/-- Odd degree cannot attain the second order: a one-regular graph would
pair an odd number of vertices. -/
theorem containsC4_of_odd_secondOrder
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hd : 4 ≤ d) (hodd : Odd d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3) :
    containsC4 V G := by
  by_contra hfree
  letI : DecidableRel (antipodalGraph G).Adj := Classical.decRel _
  have hdeg : ∀ x : V, (antipodalGraph G).degree x = 1 :=
    antipodalGraph_degree_eq_one_of_secondOrder_odd
      G hfree hd hodd hmin hcard
  have hshake := (antipodalGraph G).sum_degrees_eq_twice_card_edges
  simp_rw [hdeg] at hshake
  have hcardEven : Even (Fintype.card V) := by
    refine ⟨(antipodalGraph G).edgeFinset.card, ?_⟩
    simpa [two_mul] using hshake
  have hcardOdd : Odd (Fintype.card V) := by
    rw [hcard]
    have hprodEven : Even (d * (d - 1)) := by
      rcases Nat.even_or_odd d with he | ho
      · exact he.mul_right _
      · have : Even (d - 1) := by
          obtain ⟨a, ha⟩ := ho
          exact ⟨a, by omega⟩
        exact this.mul_left _
    obtain ⟨a, ha⟩ := hprodEven
    exact ⟨a + 1, by omega⟩
  exact (Nat.not_even_iff_odd.mpr hcardOdd) hcardEven

/-- Odd-degree strict Moore bound sharpened through the second order. -/
theorem mul_pred_add_four_le_card_of_c4Free_minDegree_odd
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hd : 4 ≤ d) (hodd : Odd d)
    (hmin : d ≤ G.minDegree) (hfree : ¬ containsC4 V G) :
    d * (d - 1) + 4 ≤ Fintype.card V := by
  have hbase := second_strict_moore_bound G hfree (by omega) hmin
  by_contra hnot
  have heq : Fintype.card V = d * (d - 1) + 3 := by omega
  exact hfree (containsC4_of_odd_secondOrder G hd hodd hmin heq)

/-- Threshold form of the odd second-order exclusion. -/
theorem minDegreeForC4_secondOrder_le_of_odd
    {d : ℕ} (hd : 4 ≤ d) (hodd : Odd d) :
    minDegreeForC4 (d * (d - 1) + 3) ≤ d := by
  apply Nat.sInf_le
  intro G _ hmin
  exact containsC4_of_odd_secondOrder G hd hodd hmin (by simp)

end

end Erdos85
