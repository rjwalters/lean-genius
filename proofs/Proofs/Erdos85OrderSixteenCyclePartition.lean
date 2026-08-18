import Mathlib

/-! # Census of cycle partitions of order sixteen

The internal graph on the exceptional order-sixteen block is a disjoint
union of cycles.  C4-freeness excludes length four, leaving exactly the
twelve partitions recorded here.
-/

namespace Erdos85

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- The twelve nonincreasing partitions of sixteen into cycle lengths at
least three, excluding a four-cycle. -/
def OrderSixteenCyclePartition (l : List ℕ) : Prop :=
  l = [16] ∨
  l = [13, 3] ∨
  l = [11, 5] ∨
  l = [10, 6] ∨
  l = [10, 3, 3] ∨
  l = [9, 7] ∨
  l = [8, 8] ∨
  l = [8, 5, 3] ∨
  l = [7, 6, 3] ∨
  l = [7, 3, 3, 3] ∨
  l = [6, 5, 5] ∨
  l = [5, 5, 3, 3]

/-- A nonincreasing list of admissible cycle lengths with total order
sixteen is one of the twelve explicit partitions. -/
theorem orderSixteen_cycle_partition_classification
    (l : List ℕ) (hsum : l.sum = 16)
    (hparts : ∀ r ∈ l, 3 ≤ r ∧ r ≠ 4)
    (hsorted : l.Pairwise (· ≥ ·)) :
    OrderSixteenCyclePartition l := by
  rcases l with _ | ⟨a, l⟩
  · simp at hsum
  rcases l with _ | ⟨b, l⟩
  · simp only [List.sum_cons, List.sum_nil, add_zero] at hsum
    simp only [List.mem_cons, List.mem_singleton, forall_eq_or_imp,
      forall_eq] at hparts
    simp [OrderSixteenCyclePartition, hsum]
  rcases l with _ | ⟨c, l⟩
  · simp only [List.sum_cons, List.sum_nil, add_zero] at hsum
    simp only [List.mem_cons, List.mem_singleton, forall_eq_or_imp,
      forall_eq] at hparts
    simp only [List.pairwise_cons, List.pairwise_singleton, and_true,
      List.mem_singleton, forall_eq] at hsorted
    have ha : a ≤ 16 := by omega
    have hb : b ≤ 16 := by omega
    interval_cases a <;> try omega
    all_goals interval_cases b <;> simp [OrderSixteenCyclePartition] at *
  rcases l with _ | ⟨d, l⟩
  · simp only [List.sum_cons, List.sum_nil, add_zero] at hsum
    simp only [List.mem_cons, List.mem_singleton, forall_eq_or_imp,
      forall_eq] at hparts
    simp only [List.pairwise_cons, List.pairwise_singleton, and_true,
      List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq] at hsorted
    have ha : a ≤ 16 := by omega
    have hb : b ≤ 16 := by omega
    have hc : c ≤ 16 := by omega
    interval_cases a <;> try omega
    all_goals interval_cases b <;> try omega
    all_goals interval_cases c <;> simp [OrderSixteenCyclePartition] at *
  rcases l with _ | ⟨e, l⟩
  · simp only [List.sum_cons, List.sum_nil, add_zero] at hsum
    simp only [List.mem_cons, List.mem_singleton, forall_eq_or_imp,
      forall_eq] at hparts
    simp only [List.pairwise_cons, List.pairwise_singleton, and_true,
      List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq] at hsorted
    have ha : a ≤ 16 := by omega
    have hb : b ≤ 16 := by omega
    have hc : c ≤ 16 := by omega
    have hd : d ≤ 16 := by omega
    interval_cases a <;> try omega
    all_goals interval_cases b <;> try omega
    all_goals interval_cases c <;> try omega
    all_goals interval_cases d <;> simp [OrderSixteenCyclePartition] at *
  rcases l with _ | ⟨f, l⟩
  · have : 3 + 3 + 3 + 3 + 3 ≤ a + b + c + d + e := by
      have ha := (hparts a (by simp)).1
      have hb := (hparts b (by simp)).1
      have hc := (hparts c (by simp)).1
      have hd := (hparts d (by simp)).1
      have he := (hparts e (by simp)).1
      omega
    simp only [List.sum_cons, List.sum_nil, add_zero] at hsum
    simp only [List.mem_cons, List.mem_singleton, forall_eq_or_imp,
      forall_eq] at hparts
    simp only [List.pairwise_cons, List.pairwise_singleton, and_true,
      List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq] at hsorted
    have ha : a ≤ 16 := by omega
    have hb : b ≤ 16 := by omega
    have hc : c ≤ 16 := by omega
    have hd : d ≤ 16 := by omega
    have he : e ≤ 16 := by omega
    interval_cases a <;> try omega
    all_goals interval_cases b <;> try omega
    all_goals interval_cases c <;> try omega
    all_goals interval_cases d <;> try omega
    all_goals interval_cases e <;> simp [OrderSixteenCyclePartition] at *
  · have ha := (hparts a (by simp)).1
    have hb := (hparts b (by simp)).1
    have hc := (hparts c (by simp)).1
    have hd := (hparts d (by simp)).1
    have he := (hparts e (by simp)).1
    have hf := (hparts f (by simp)).1
    simp only [List.sum_cons] at hsum
    have htail : 0 ≤ l.sum := Nat.zero_le _
    omega

end Erdos85
