/-
  Aristotle companion for Erdős Problem #613: Graph Decomposition and Size Ramsey Numbers

  This file exposes routine lemmas for automated proof search by Aristotle.
  The main formalization is in Erdos613Problem.lean.

  Targets: arithmetic lemmas about criticalEdgeCount that do not depend on
  sorry-defined graph functions.
-/

import Mathlib
import Proofs.Erdos613Problem

open scoped Classical

namespace Erdos613Aristotle

open Erdos613 Nat

/-- criticalEdgeCount equals 3n(n+1)/2 - 1 (equivalently n²+n+n(n+1)/2-1).
    This is a pure binomial coefficient identity: C(2n+1,2) - C(n,2) - 1.
    (v4.31 migration: `omega` cannot see through the nonlinear `Nat.choose_two_right`
    division atoms; substitute `n = m + 1` to eliminate the truncated subtraction,
    convert the two half-integer divisions to exact-doubled equalities via
    `Nat.div_two_mul_two_of_even`, then let `omega` finish over the resulting
    linear combination of the shared `m*m` atom.) -/
theorem critical_edge_count_formula_ari (n : ℕ) (hn : n ≥ 1) :
    criticalEdgeCount n = n * n + n + (n * (n + 1)) / 2 - 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  simp only [criticalEdgeCount, Nat.choose_two_right]
  have hs1 : 1 + m - 1 = m := by omega
  have hs2 : 2 * (1 + m) + 1 - 1 = 2 * (1 + m) := by omega
  rw [hs1, hs2]
  have e6 : (2 * (1 + m) + 1) * (2 * (1 + m)) / 2 = (2 * (1 + m) + 1) * (1 + m) := by
    rw [Nat.mul_div_assoc (2 * (1 + m) + 1) ⟨1 + m, rfl⟩,
        Nat.mul_div_cancel_left (1 + m) (by norm_num)]
  rw [e6]
  have hev1 : Even ((1 + m) * m) := by
    have h := Nat.even_mul_pred_self (1 + m)
    rwa [hs1] at h
  have hev2 : Even ((1 + m) * (1 + m + 1)) := Nat.even_mul_succ_self (1 + m)
  have e1 : (1 + m) * m / 2 * 2 = (1 + m) * m := Nat.div_two_mul_two_of_even hev1
  have e2 : (1 + m) * (1 + m + 1) / 2 * 2 = (1 + m) * (1 + m + 1) :=
    Nat.div_two_mul_two_of_even hev2
  ring_nf
  ring_nf at e1 e2
  omega

/-- criticalEdgeCount is strictly increasing for n ≥ 1 -/
theorem criticalEdgeCount_mono (n : ℕ) (hn : n ≥ 1) :
    criticalEdgeCount n < criticalEdgeCount (n + 1) := by
  rw [critical_edge_count_formula_ari n hn, critical_edge_count_formula_ari (n + 1) (by omega)]
  have hev1 : Even (n * (n + 1)) := Nat.even_mul_succ_self n
  have hev2 : Even ((n + 1) * (n + 1 + 1)) := Nat.even_mul_succ_self (n + 1)
  have e1 : n * (n + 1) / 2 * 2 = n * (n + 1) := Nat.div_two_mul_two_of_even hev1
  have e2 : (n + 1) * (n + 1 + 1) / 2 * 2 = (n + 1) * (n + 1 + 1) :=
    Nat.div_two_mul_two_of_even hev2
  ring_nf
  ring_nf at e1 e2
  omega

/-- criticalEdgeCount n ≥ 2 for all n ≥ 1 -/
theorem criticalEdgeCount_pos (n : ℕ) (hn : n ≥ 1) :
    criticalEdgeCount n ≥ 2 := by
  rw [critical_edge_count_formula_ari n hn]
  have hev1 : Even (n * (n + 1)) := Nat.even_mul_succ_self n
  have e1 : n * (n + 1) / 2 * 2 = n * (n + 1) := Nat.div_two_mul_two_of_even hev1
  ring_nf
  ring_nf at e1
  omega

end Erdos613Aristotle
