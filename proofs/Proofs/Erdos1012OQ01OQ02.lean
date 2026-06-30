/-
  Erdős Problem #1012 — OQ-01-OQ-02: structural arithmetic of the edge threshold in n

  The parent `Erdos1012OQ01` formalizes the Woodall function `f(k)` and the edge
  threshold

      edgeThreshold n k = C(n-k-1, 2) + C(k+2, 2) + 1,

  evaluating it at the boundary points `n = 2k+2` and `n = 2k+3` (`threshold_at_extremal`,
  `threshold_symmetric`, `threshold_diff`).  What the parent does *not* record is how
  the threshold behaves as `n` varies — yet that monotonicity is exactly what makes
  `f(k)` a well-defined "minimum `n₀`": the edge requirement tightens with each extra
  vertex.  This file supplies that structure.

  * `edgeThreshold_eq`        — the explicit polynomial form
    `(n-k-1)(n-k-2)/2 + (k+2)(k+1)/2 + 1`.
  * `edgeThreshold_succ_left` — the **recurrence in `n`** (for `n ≥ k+1`):
    `edgeThreshold (n+1) k = edgeThreshold n k + (n-k-1)`.  Adding a vertex raises
    the threshold by exactly `n-k-1` (the discrete derivative `C(m+1,2)-C(m,2)=m`).
  * `edgeThreshold_lt_succ` / `edgeThreshold_mono` — strict and weak monotonicity
    in `n` on the meaningful range `n ≥ k+2` / `n ≥ k+1`.

  All results are fully machine-checked (0 axioms, 0 sorries), reusing the parent's
  `edgeThreshold` definition.

  Reference: Woodall (1972); https://erdosproblems.com/1012
-/

import Mathlib
import Proofs.Erdos1012OQ01

namespace Erdos1012OQ01OQ02

open Erdos1012OQ01

/-- Pascal's discrete-derivative identity for the second binomial coefficient:
    `C(m+1, 2) = C(m, 2) + m`. -/
theorem choose_two_succ (m : ℕ) : (m + 1).choose 2 = m.choose 2 + m := by
  rw [Nat.choose_succ_succ m 1, Nat.choose_one_right]
  show m + m.choose 2 = m.choose 2 + m
  omega

/-- **Explicit polynomial form of the edge threshold.** -/
theorem edgeThreshold_eq (n k : ℕ) :
    edgeThreshold n k =
      (n - k - 1) * (n - k - 2) / 2 + (k + 2) * (k + 1) / 2 + 1 := by
  unfold edgeThreshold
  have e1 : n - k - 1 - 1 = n - k - 2 := by omega
  have e2 : k + 2 - 1 = k + 1 := by omega
  rw [Nat.choose_two_right, Nat.choose_two_right, e1, e2]

/-- **Recurrence in `n`.**  For `n ≥ k+1`, adding one vertex raises the threshold
    by exactly `n - k - 1`:  `edgeThreshold (n+1) k = edgeThreshold n k + (n-k-1)`.
    This is the discrete derivative `C(m+1,2) − C(m,2) = m` with `m = n-k-1`. -/
theorem edgeThreshold_succ_left (n k : ℕ) (h : k + 1 ≤ n) :
    edgeThreshold (n + 1) k = edgeThreshold n k + (n - k - 1) := by
  unfold edgeThreshold
  have e : n + 1 - k - 1 = (n - k - 1) + 1 := by omega
  rw [e, choose_two_succ (n - k - 1)]
  ring

/-- **Strict monotonicity in `n`.**  On the meaningful range `n ≥ k+2` (so the
    leading binomial coefficient is genuinely growing), the threshold strictly
    increases with each added vertex. -/
theorem edgeThreshold_lt_succ (n k : ℕ) (h : k + 2 ≤ n) :
    edgeThreshold n k < edgeThreshold (n + 1) k := by
  rw [edgeThreshold_succ_left n k (by omega)]
  omega

/-- **Weak monotonicity in `n`.**  For `k+1 ≤ n ≤ m`,
    `edgeThreshold n k ≤ edgeThreshold m k`. -/
theorem edgeThreshold_mono (k : ℕ) {n m : ℕ} (hn : k + 1 ≤ n) (hnm : n ≤ m) :
    edgeThreshold n k ≤ edgeThreshold m k := by
  induction hnm with
  | refl => exact le_refl _
  | @step m h ih =>
    have hkm : k + 1 ≤ m := le_trans hn h
    rw [edgeThreshold_succ_left m k hkm]
    omega

end Erdos1012OQ01OQ02
