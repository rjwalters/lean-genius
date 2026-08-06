import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Balancing blocks of size at most two

The local graph induced by the neighbours of a vertex in a `C₄`-free graph
has maximum degree one.  Its connected components therefore have size one or
two.  This file isolates the arithmetic part of splitting those components:
a list of blocks of size at most two can be cut between blocks with at most
one unit of overshoot.
-/

namespace Erdos85

/-- A list of natural-number weights, each at most two, has a prefix whose
sum first reaches a prescribed target and overshoots it by at most one. -/
theorem exists_take_sum_between_of_le_two
    (weights : List ℕ) (target : ℕ)
    (hpos : ∀ w ∈ weights, 1 ≤ w)
    (hle : ∀ w ∈ weights, w ≤ 2)
    (htotal : target ≤ weights.sum) :
    ∃ k, target ≤ (weights.take k).sum ∧
      (weights.take k).sum ≤ target + 1 := by
  induction weights generalizing target with
  | nil =>
      simp only [List.sum_nil] at htotal
      have ht : target = 0 := Nat.eq_zero_of_le_zero htotal
      subst target
      exact ⟨0, by simp⟩
  | cons w weights ih =>
      by_cases ht0 : target = 0
      · subst target
        exact ⟨0, by simp⟩
      by_cases htw : target ≤ w
      · refine ⟨1, ?_, ?_⟩
        · simpa using htw
        · change w ≤ target + 1
          have hwpos := hpos w (by simp)
          have hwle := hle w (by simp)
          clear htotal
          omega
      · have hwt : w < target := Nat.lt_of_not_ge htw
        have htail : target - w ≤ weights.sum := by
          change target ≤ w + weights.sum at htotal
          have hsub : target - w + w = target :=
            Nat.sub_add_cancel (Nat.le_of_lt hwt)
          omega
        obtain ⟨k, hklo, hkhi⟩ := ih (target - w)
          (fun a ha => hpos a (by simp [ha]))
          (fun a ha => hle a (by simp [ha])) htail
        refine ⟨k + 1, ?_, ?_⟩
        · simp only [List.take_succ_cons, List.sum_cons]
          omega
        · simp only [List.take_succ_cons, List.sum_cons]
          omega

/-- If the total block weight is at least `2 * target + 1`, a cut between
blocks leaves weight at least `target` on both sides. -/
theorem exists_take_balanced_of_le_two
    (weights : List ℕ) (target : ℕ)
    (hpos : ∀ w ∈ weights, 1 ≤ w)
    (hle : ∀ w ∈ weights, w ≤ 2)
    (htotal : 2 * target + 1 ≤ weights.sum) :
    ∃ k, target ≤ (weights.take k).sum ∧
      target ≤ (weights.drop k).sum := by
  have htarget : target ≤ weights.sum := by omega
  obtain ⟨k, hklo, hkhi⟩ :=
    exists_take_sum_between_of_le_two weights target hpos hle htarget
  refine ⟨k, hklo, ?_⟩
  have hsum : (weights.take k).sum + (weights.drop k).sum = weights.sum := by
    rw [← List.sum_append, List.take_append_drop]
  rw [← hsum] at htotal
  omega

/-- Numerical core of the parity refinement.  From `q` blocks of weight two
and `r` blocks of weight one, a target can be represented exactly provided
the total is at least twice the target and either the target is even or a
weight-one block exists. -/
theorem exists_two_one_count_exact
    (q r target : ℕ) (htotal : 2 * target ≤ 2 * q + r)
    (hparity : target % 2 = 0 ∨ 1 ≤ r) :
    ∃ a b, a ≤ q ∧ b ≤ r ∧ 2 * a + b = target := by
  by_cases hq : 2 * q ≤ target
  · refine ⟨q, target - 2 * q, Nat.le_refl q, ?_, ?_⟩ <;> omega
  · refine ⟨target / 2, target % 2, ?_, ?_, ?_⟩
    · omega
    · rcases hparity with htEven | hr
      · simpa [htEven]
      · have hmod : target % 2 < 2 := Nat.mod_lt _ (by omega)
        omega
    · omega

end Erdos85
