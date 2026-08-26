import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalSemantics
import Proofs.Erdos85OrderFortyNineHighIncidenceCensus
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-! # Ambient order-49 structure recovered from canonical semantics

The canonical SAT semantics state low-low degrees and fixed high support
separately.  This file recombines them into ordinary graph degrees: canonical
high vertices have degree eight and canonical low vertices degree seven.
Consequently the semantic graph itself is an order-49 near-regular graph with
exactly seven high vertices, allowing the existing quotient theorems to be
reused without assuming provenance from an earlier graph.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

def sevenHighT0CanonicalLowIndexSupport
    (i : SevenHighT0LowIndex) : Finset (Fin 7) :=
  match i with
  | Sum.inl _ => ∅
  | Sum.inr (Sum.inl q) => {q.1}
  | Sum.inr (Sum.inr key) => {key.1.1, key.1.2}

@[simp] theorem sevenHighT0CanonicalLowIndexSupport_card
    (i : SevenHighT0LowIndex) :
    (sevenHighT0CanonicalLowIndexSupport i).card =
      sevenHighT0LowIndexSupportCard i := by
  rcases i with i | i
  · simp [sevenHighT0CanonicalLowIndexSupport,
      sevenHighT0LowIndexSupportCard]
  · rcases i with i | i
    · simp [sevenHighT0CanonicalLowIndexSupport,
        sevenHighT0LowIndexSupportCard]
    · simp [sevenHighT0CanonicalLowIndexSupport,
        sevenHighT0LowIndexSupportCard, ne_of_lt i.2]

theorem SevenHighT0CanonicalCompletionSemantics.high_low_adj_iff_mem_support
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (hH : SevenHighT0CanonicalCompletionSemantics H)
    (w : Fin 7) (i : SevenHighT0LowIndex) :
    H.Adj (Sum.inl w) (Sum.inr i) ↔
      w ∈ sevenHighT0CanonicalLowIndexSupport i := by
  rcases i with i | i
  · simp [sevenHighT0CanonicalLowIndexSupport, hH.high_empty]
  · rcases i with i | i
    · simp [sevenHighT0CanonicalLowIndexSupport, hH.high_singleton]
    · rw [hH.high_pair]
      simp [sevenHighT0CanonicalLowIndexSupport]

private theorem sum_indicator_mem_eq_card
    {α : Type*} [Fintype α] [DecidableEq α] (S : Finset α) :
    (∑ x : α, if x ∈ S then 1 else 0) = S.card := by
  simp

theorem SevenHighT0CanonicalCompletionSemantics.highNeighbor_indicator_sum
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (hH : SevenHighT0CanonicalCompletionSemantics H)
    (i : SevenHighT0LowIndex) :
    (∑ w : Fin 7, if H.Adj (Sum.inr i) (Sum.inl w) then 1 else 0) =
      sevenHighT0LowIndexSupportCard i := by
  calc
    (∑ w : Fin 7, if H.Adj (Sum.inr i) (Sum.inl w) then 1 else 0) =
        ∑ w : Fin 7,
          if w ∈ sevenHighT0CanonicalLowIndexSupport i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro w _
      simp only [H.adj_comm (Sum.inr i) (Sum.inl w),
        hH.high_low_adj_iff_mem_support]
    _ = (sevenHighT0CanonicalLowIndexSupport i).card :=
      sum_indicator_mem_eq_card _
    _ = sevenHighT0LowIndexSupportCard i :=
      sevenHighT0CanonicalLowIndexSupport_card i

/-- Full graph degree of every canonical low vertex. -/
theorem SevenHighT0CanonicalCompletionSemantics.low_degree_full
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (hH : SevenHighT0CanonicalCompletionSemantics H)
    (i : SevenHighT0LowIndex) :
    H.degree (Sum.inr i) = 7 := by
  calc
    H.degree (Sum.inr i) =
        ∑ x : SevenHighT0CanonicalIndex,
          if H.Adj (Sum.inr i) x then 1 else 0 :=
      H.degree_eq_sum_if_adj (R := Nat) (Sum.inr i)
    _ = (∑ w : Fin 7,
          if H.Adj (Sum.inr i) (Sum.inl w) then 1 else 0) +
        ∑ j : SevenHighT0LowIndex,
          if H.Adj (Sum.inr i) (Sum.inr j) then 1 else 0 := by
      rw [Fintype.sum_sum_type]
    _ = sevenHighT0LowIndexSupportCard i +
        ∑ j : SevenHighT0LowIndex,
          if H.Adj (Sum.inr i) (Sum.inr j) then 1 else 0 := by
      rw [hH.highNeighbor_indicator_sum]
    _ = sevenHighT0LowIndexSupportCard i + (H.comap Sum.inr).degree i := by
      have hlow := (H.comap Sum.inr).degree_eq_sum_if_adj (R := Nat) i
      change (H.comap Sum.inr).degree i =
        ∑ j : SevenHighT0LowIndex,
          if H.Adj (Sum.inr i) (Sum.inr j) then 1 else 0 at hlow
      rw [← hlow]
    _ = 7 := by simpa [Nat.add_comm] using hH.low_degree i

private theorem sevenHighT0Canonical_support_incidence_sum (w : Fin 7) :
    (∑ i : SevenHighT0LowIndex,
      if w ∈ sevenHighT0CanonicalLowIndexSupport i then 1 else 0) = 8 := by
  fin_cases w <;> decide

/-- Full graph degree of every canonical high vertex. -/
theorem SevenHighT0CanonicalCompletionSemantics.high_degree_full
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (hH : SevenHighT0CanonicalCompletionSemantics H)
    (w : Fin 7) :
    H.degree (Sum.inl w) = 8 := by
  rw [show H.degree (Sum.inl w) =
      ∑ x : SevenHighT0CanonicalIndex,
        if H.Adj (Sum.inl w) x then 1 else 0 from
    H.degree_eq_sum_if_adj (R := Nat) (Sum.inl w)]
  rw [Fintype.sum_sum_type]
  have hhigh :
      (∑ z : Fin 7, if H.Adj (Sum.inl w) (Sum.inl z) then 1 else 0) = 0 := by
    simp [hH.high_high]
  rw [hhigh, zero_add]
  calc
    (∑ i : SevenHighT0LowIndex,
      if H.Adj (Sum.inl w) (Sum.inr i) then 1 else 0) =
        ∑ i : SevenHighT0LowIndex,
          if w ∈ sevenHighT0CanonicalLowIndexSupport i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [hH.high_low_adj_iff_mem_support]
    _ = 8 := sevenHighT0Canonical_support_incidence_sum w

theorem SevenHighT0CanonicalCompletionSemantics.degree_eq_seven_or_eight
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (hH : SevenHighT0CanonicalCompletionSemantics H)
    (x : SevenHighT0CanonicalIndex) :
    H.degree x = 7 ∨ H.degree x = 8 := by
  rcases x with w | i
  · exact Or.inr (hH.high_degree_full w)
  · exact Or.inl (hH.low_degree_full i)

theorem SevenHighT0CanonicalCompletionSemantics.minDegree_seven
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (hH : SevenHighT0CanonicalCompletionSemantics H) :
    ∀ x, 7 ≤ H.degree x := by
  intro x
  rcases hH.degree_eq_seven_or_eight x with h | h <;> omega

/-- The degree-eight sector is exactly the seven canonical high indices. -/
theorem SevenHighT0CanonicalCompletionSemantics.mem_highVertices_iff
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (hH : SevenHighT0CanonicalCompletionSemantics H)
    (x : SevenHighT0CanonicalIndex) :
    x ∈ orderFortyNineHighVertices H ↔ ∃ w : Fin 7, x = Sum.inl w := by
  rw [orderFortyNineHighVertices, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rcases x with w | i
  · simp [hH.high_degree_full]
  · simp [hH.low_degree_full]

theorem SevenHighT0CanonicalCompletionSemantics.highVertices_card
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (hH : SevenHighT0CanonicalCompletionSemantics H) :
    (orderFortyNineHighVertices H).card = 7 := by
  change (orderFortyNineHighVertices H).card = (Finset.univ : Finset (Fin 7)).card
  apply Eq.symm
  apply Finset.card_bij (fun w _ => Sum.inl w)
  · intro w _
    exact (hH.mem_highVertices_iff (Sum.inl w)).2 ⟨w, rfl⟩
  · intro a _ b _ hab
    exact Sum.inl.inj hab
  · intro x hx
    obtain ⟨w, rfl⟩ := (hH.mem_highVertices_iff x).1 hx
    exact ⟨w, Finset.mem_univ w, rfl⟩

end


end Erdos85

#print axioms Erdos85.SevenHighT0CanonicalCompletionSemantics.low_degree_full
#print axioms Erdos85.SevenHighT0CanonicalCompletionSemantics.high_degree_full
#print axioms Erdos85.SevenHighT0CanonicalCompletionSemantics.highVertices_card
