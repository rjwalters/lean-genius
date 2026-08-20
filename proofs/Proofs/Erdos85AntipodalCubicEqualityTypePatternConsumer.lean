import Proofs.Erdos85AntipodalCubicEqualityTypePatterns
import Proofs.Erdos85CubicResidualValueTypeHandshake
import Proofs.Erdos85MuNegThreeZeroFiveShoreTypePopulations

/-! # Graph-facing antipodal sharp-equality type patterns -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

private theorem filter_three_card_add_filter_four_card
    {α : Type*} [DecidableEq α] (Q : Finset α) (f : α → ℕ)
    (h34 : ∀ x ∈ Q, f x = 3 ∨ f x = 4) :
    (Q.filter fun x ↦ f x = 3).card +
      (Q.filter fun x ↦ f x = 4).card = Q.card := by
  classical
  induction Q using Finset.induction_on with
  | empty => simp
  | @insert a Q ha ih =>
      have hi := ih (fun x hx ↦ h34 x (Finset.mem_insert_of_mem hx))
      rcases h34 a (Finset.mem_insert_self a Q) with h3 | h4
      · simp [Finset.filter_insert, ha, h3]
        omega
      · simp [Finset.filter_insert, ha, h4]
        omega

theorem residualShoreType_card_add_neighborCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (S : Finset V) (t : ℕ) (a : R.edgeFinset) :
    ((shoreTypeEdgeFinset R S t).filter fun b ↦ ¬ Cedge.Adj b a).card +
      serviceNeighborShoreTypeCount R Cedge a S t =
        (shoreTypeEdgeFinset R S t).card := by
  classical
  let T := shoreTypeEdgeFinset R S t
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := T) (p := fun b ↦ Cedge.Adj b a)
  have hadj : (T.filter fun b ↦ Cedge.Adj b a).card =
      serviceNeighborShoreTypeCount R Cedge a S t := by
    congr 1
    ext b
    simp [T, shoreTypeEdgeFinset, SimpleGraph.mem_neighborFinset,
      Cedge.adj_comm, and_comm]
  rw [hadj] at hsplit
  simpa [T, add_comm] using hsplit

theorem residualCubicValueShoreTypeFinset_compl_two_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (S : Finset V) (q : ℕ) (a : R.edgeFinset) :
    residualCubicValueShoreTypeFinset R Cedge Sᶜ 2 q a =
      residualCubicValueShoreTypeFinset R Cedge S 0 q a := by
  unfold residualCubicValueShoreTypeFinset
  rw [← shoreTypeEdgeFinset_zero_eq_two_compl R S]

theorem residualCubicValueShoreTypeFinset_compl_one_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (S : Finset V) (q : ℕ) (a : R.edgeFinset) :
    residualCubicValueShoreTypeFinset R Cedge Sᶜ 1 q a =
      residualCubicValueShoreTypeFinset R Cedge S 1 q a := by
  classical
  ext b
  simp only [residualCubicValueShoreTypeFinset, shoreTypeEdgeFinset,
    Finset.mem_filter, Finset.mem_univ, true_and]
  have hsplit := Finset.card_inter_add_card_sdiff b.1.toFinset S
  have hcomp : (b.1.toFinset ∩ Sᶜ).card =
      (b.1.toFinset \ S).card := by
    congr 1
    ext x
    simp
  have hedge := R.card_toFinset_mem_edgeFinset b
  rw [hcomp]
  have htype : (b.1.toFinset \ S).card = 1 ↔
      (b.1.toFinset ∩ S).card = 1 := by omega
  rw [htype]

set_option maxHeartbeats 1000000 in
/-- Once every residual cubic entry is a three or four, the sharp local
value-four incidences `32/16` force the finite antipodal type patterns. -/
theorem antipodal_cubicEquality_graph_typePattern
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (S : Finset V) (a : R.edgeFinset)
    (hpop0 : (shoreTypeEdgeFinset R S 0).card = 12)
    (hpop2 : (shoreTypeEdgeFinset R S 2).card = 12)
    (hc2 : serviceNeighborShoreTypeCount R Cedge a S 2 = 0 ∨
      serviceNeighborShoreTypeCount R Cedge a S 2 = 1 ∨
      serviceNeighborShoreTypeCount R Cedge a S 2 = 2)
    (hprofile : serviceNeighborShoreTypeCount R Cedge a S 0 =
      serviceNeighborShoreTypeCount R Cedge a S 2 + 2)
    (hS4 : (∑ u ∈ S, cubicResidualFiberHistogram R Cedge u a 4) = 32)
    (hSc4 : (∑ u ∈ Sᶜ, cubicResidualFiberHistogram R Cedge u a 4) = 16)
    (h34 : ∀ b ∈ (Finset.univ : Finset R.edgeFinset),
      ¬ Cedge.Adj b a →
      residualFiberCubicWalkCount R Cedge a b = 3 ∨
        residualFiberCubicWalkCount R Cedge a b = 4) :
    let c2 := serviceNeighborShoreTypeCount R Cedge a S 2
    let r0 := (residualCubicValueShoreTypeFinset R Cedge S 0 4 a).card
    let r2 := (residualCubicValueShoreTypeFinset R Cedge S 2 4 a).card
    let s0 := (residualCubicValueShoreTypeFinset R Cedge S 0 3 a).card
    let s2 := (residualCubicValueShoreTypeFinset R Cedge S 2 3 a).card
    r2 = r0 + 8 ∧ s0 = s2 + 6 ∧
      ((c2 = 0 ∧ r0 ≤ 4) ∨ (c2 = 1 ∧ r0 ≤ 3) ∨
        (c2 = 2 ∧ r0 ≤ 2)) := by
  classical
  dsimp only
  let c0 := serviceNeighborShoreTypeCount R Cedge a S 0
  let c2 := serviceNeighborShoreTypeCount R Cedge a S 2
  let Q (t : ℕ) := (shoreTypeEdgeFinset R S t).filter fun b ↦ ¬ Cedge.Adj b a
  let r (t : ℕ) := (residualCubicValueShoreTypeFinset R Cedge S t 4 a).card
  let s (t : ℕ) := (residualCubicValueShoreTypeFinset R Cedge S t 3 a).card
  let r1 := r 1
  have hshore := sum_cubicResidualFiberHistogram_eq_two_typeTwo_add_typeOne
    R Cedge S 4 a
  rw [hS4] at hshore
  have hcomp := sum_cubicResidualFiberHistogram_eq_two_typeTwo_add_typeOne
    R Cedge Sᶜ 4 a
  rw [hSc4, residualCubicValueShoreTypeFinset_compl_two_eq_zero,
    residualCubicValueShoreTypeFinset_compl_one_eq_one] at hcomp
  have hn0 := residualShoreType_card_add_neighborCount R Cedge S 0 a
  have hn2 := residualShoreType_card_add_neighborCount R Cedge S 2 a
  rw [hpop0] at hn0
  rw [hpop2] at hn2
  have hpart (t : ℕ) : r t + s t = (Q t).card := by
    let f := residualFiberCubicWalkCount R Cedge a
    have hall : ∀ b ∈ Q t, f b = 3 ∨ f b = 4 := by
      intro b hb
      exact h34 b (Finset.mem_univ b) (Finset.mem_filter.mp hb).2
    have hp := filter_three_card_add_filter_four_card (Q t) f hall
    have hthree : (Q t).filter (fun b ↦ f b = 3) =
        residualCubicValueShoreTypeFinset R Cedge S t 3 a := by
      ext b
      simp only [Q, f, residualCubicValueShoreTypeFinset,
        Finset.mem_filter]
      tauto
    have hfour : (Q t).filter (fun b ↦ f b = 4) =
        residualCubicValueShoreTypeFinset R Cedge S t 4 a := by
      ext b
      simp only [Q, f, residualCubicValueShoreTypeFinset,
        Finset.mem_filter]
      tauto
    rw [hthree, hfour] at hp
    simpa [r, s, add_comm] using hp
  apply antipodal_cubicEquality_typePattern c0 c2 (Q 0).card (Q 2).card
    (r 0) r1 (r 2) (s 0) (s 2)
  · simpa [c2] using hc2
  · simpa [c0, c2] using hprofile
  · simpa [Q, c0] using hn0
  · simpa [Q, c2] using hn2
  · exact hpart 0
  · exact hpart 2
  · simpa [r, r1] using hshore.symm
  · simpa [r, r1, add_comm] using hcomp.symm

end

end Erdos85

#print axioms Erdos85.antipodal_cubicEquality_graph_typePattern
