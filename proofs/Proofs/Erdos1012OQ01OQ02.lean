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
  * `edgeThreshold_add_surplus_eq_choose_two` — the **exact surplus** below the complete
    graph: `C(n,2) = edgeThreshold n k + (k(k+2) + (n-(2k+3))(k+1))` for `n ≥ 2k+3`,
    upgrading `edgeThreshold_le_choose_two` from an inequality to an equality.
  * `edgeThreshold_lt_choose_two` — **strict** non-degeneracy: `edgeThreshold n k < C(n,2)`
    on `n ≥ 2k+3` away from the single degenerate corner `(k,n) = (0,3)`.

  It also records the complementary variation in the *cycle-length parameter `k`* (with
  `n` fixed), which the parent likewise omits:

  * `edgeThreshold_succ_right`   — the **recurrence in `k`** (for `n ≥ k+2`):
    `edgeThreshold n (k+1) + (n-k-2) = edgeThreshold n k + (k+2)`; the discrete
    derivative in `k` is `2k+4-n`, negative for small `k` and positive for large `k`.
  * `edgeThreshold_succ_right_le` / `edgeThreshold_succ_right_ge` — the threshold
    **decreases** in `k` on `n ≥ 2k+4` and **increases** on `k+2 ≤ n ≤ 2k+4`.
  * `edgeThreshold_second_diff`  — **convexity**: the second difference in `k` is the
    constant `+2` (`edgeThreshold n k + edgeThreshold n (k+2) = 2·edgeThreshold n (k+1)+2`),
    so `k ↦ edgeThreshold n k` is U-shaped.
  * `edgeThreshold_reflect`      — **reflection symmetry** `edgeThreshold n k =
    edgeThreshold n (n-k-3)` (the involution `k ↦ n-k-3` swaps the two binomials),
    which with convexity pins the minimum to the axis `k = (n-3)/2`.

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

/-- Doubled second binomial coefficient: `2 * C(m, 2) = m * (m - 1)` (over ℕ,
    subtraction-free once `m` is a successor). -/
theorem two_mul_choose_two (m : ℕ) : 2 * m.choose 2 = m * (m - 1) := by
  induction m with
  | zero => rfl
  | succ p ih =>
    rw [choose_two_succ, Nat.mul_add, ih, Nat.add_sub_cancel]
    cases p with
    | zero => rfl
    | succ q => simp only [Nat.succ_sub_one]; ring

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

/-!
### Variation in `k` (fixed `n`)

The results above track how `edgeThreshold n k` moves as the vertex count `n` grows.
The complementary direction — how it moves as the cycle-length parameter `k` grows with
`n` held fixed — is governed by the *other* binomial coefficient.  Writing
`edgeThreshold n k = C(n-k-1, 2) + C(k+2, 2) + 1`, increasing `k` by one *shrinks* the
first coefficient (its argument `n-k-1` drops) while it *grows* the second (`k+2` rises),
so the threshold is a sum of a decreasing and an increasing term.  The net discrete
derivative in `k` is `(k+2) - (n-k-2) = 2k+4-n`: negative for small `k`, positive for
large `k`.  Hence `k ↦ edgeThreshold n k` is **convex (U-shaped)** in `k`, with constant
second difference `2` and a reflection symmetry about the axis `k = (n-3)/2`.
-/

/-- **Recurrence in `k`.**  For `n ≥ k+2` (so `n-k-1 ≥ 1`), the subtraction-free form of
    the discrete derivative in `k`:

        edgeThreshold n (k+1) + (n - k - 2) = edgeThreshold n k + (k + 2).

    Equivalently `edgeThreshold n (k+1) − edgeThreshold n k = (k+2) − (n-k-2) = 2k+4-n`.
    Raising `k` shrinks the leading coefficient by `n-k-2 = C(n-k-1,2)-C(n-k-2,2)` and
    grows the trailing one by `k+2 = C(k+3,2)-C(k+2,2)`. -/
theorem edgeThreshold_succ_right (n k : ℕ) (h : k + 2 ≤ n) :
    edgeThreshold n (k + 1) + (n - k - 2) = edgeThreshold n k + (k + 2) := by
  unfold edgeThreshold
  have e1 : n - (k + 1) - 1 = n - k - 2 := by omega
  have e2 : k + 1 + 2 = (k + 2) + 1 := by omega
  have e3 : n - k - 1 = (n - k - 2) + 1 := by omega
  rw [e1, e2, choose_two_succ (k + 2), e3, choose_two_succ (n - k - 2)]
  omega

/-- **Threshold decreases in `k` on the pre-axis range `n ≥ 2k+4`.**  When `2k+4 ≤ n`
    the step from `k` to `k+1` lands on the decreasing (negative-derivative) branch. -/
theorem edgeThreshold_succ_right_le (n k : ℕ) (h : 2 * k + 4 ≤ n) :
    edgeThreshold n (k + 1) ≤ edgeThreshold n k := by
  have hr := edgeThreshold_succ_right n k (by omega)
  omega

/-- **Threshold increases in `k` on the post-axis range `k+2 ≤ n ≤ 2k+4`.**  When
    `n ≤ 2k+4` (and `n ≥ k+2` so the recurrence applies) the step from `k` to `k+1`
    lands on the increasing (nonnegative-derivative) branch. -/
theorem edgeThreshold_succ_right_ge (n k : ℕ) (hlo : k + 2 ≤ n) (hhi : n ≤ 2 * k + 4) :
    edgeThreshold n k ≤ edgeThreshold n (k + 1) := by
  have hr := edgeThreshold_succ_right n k hlo
  omega

/-- **Convexity in `k`: constant second difference.**  For `n ≥ k+3`,

        edgeThreshold n k + edgeThreshold n (k+2) = 2 · edgeThreshold n (k+1) + 2.

    The second discrete difference is the constant `+2`, so `k ↦ edgeThreshold n k` is
    (discretely) convex — a genuine U-shape rather than a monotone curve.  This is the
    structural reason the two single-step directions above have opposite signs. -/
theorem edgeThreshold_second_diff (n k : ℕ) (h : k + 3 ≤ n) :
    edgeThreshold n k + edgeThreshold n (k + 2)
      = 2 * edgeThreshold n (k + 1) + 2 := by
  have hA := edgeThreshold_succ_right n k (by omega)
  have hB := edgeThreshold_succ_right n (k + 1) (by omega)
  rw [show k + 1 + 1 = k + 2 from rfl] at hB
  omega

/-- **Reflection symmetry in `k`.**  For `n ≥ k+3`,

        edgeThreshold n k = edgeThreshold n (n - k - 3).

    The involution `k ↦ n-k-3` swaps the two binomial coefficients
    (`n-k-1 ↔ (n-k-3)+2` and `k+2 ↔ n-(n-k-3)-1`), so the threshold is symmetric about
    the axis `k = (n-3)/2`.  Together with `edgeThreshold_second_diff` (convexity) this
    pins the minimum of `k ↦ edgeThreshold n k` to that axis. -/
theorem edgeThreshold_reflect (n k : ℕ) (h : k + 3 ≤ n) :
    edgeThreshold n k = edgeThreshold n (n - k - 3) := by
  unfold edgeThreshold
  have e1 : n - (n - k - 3) - 1 = k + 2 := by omega
  have e2 : (n - k - 3) + 2 = n - k - 1 := by omega
  rw [e1, e2]
  ring

/-- **Non-degeneracy of the edge threshold.**  On the Woodall range `n ≥ 2k+3` the
    threshold never exceeds the total number of edges of the complete graph `Kₙ`:

        edgeThreshold n k ≤ C(n, 2).

    Hence the long-cycle hypothesis `edgeCount G ≥ edgeThreshold n k` is *satisfiable*
    (some graph on `n` vertices has that many edges) rather than vacuous — the parent's
    `hasLongCycle` is not trivially true for lack of dense enough graphs.

    Doubling both sides, the gap is exactly
    `2·(C(n,2) − edgeThreshold n k) = 2k(k+2) + 2c(k+1) ≥ 0` where `c = n − (2k+3)`. -/
theorem edgeThreshold_le_choose_two (n k : ℕ) (h : 2 * k + 3 ≤ n) :
    edgeThreshold n k ≤ n.choose 2 := by
  obtain ⟨c, rfl⟩ : ∃ c, n = 2 * k + 3 + c := ⟨n - (2 * k + 3), by omega⟩
  -- Double the threshold: 2·edgeThreshold = (k+2+c)(k+1+c) + (k+2)(k+1) + 2.
  have d1 : 2 * edgeThreshold (2 * k + 3 + c) k
      = (k + 2 + c) * (k + 1 + c) + (k + 2) * (k + 1) + 2 := by
    unfold edgeThreshold
    have h1 : 2 * (2 * k + 3 + c - k - 1).choose 2 = (k + 2 + c) * (k + 1 + c) := by
      rw [show 2 * k + 3 + c - k - 1 = k + 2 + c by omega, two_mul_choose_two,
          show k + 2 + c - 1 = k + 1 + c by omega]
    have h2 : 2 * (k + 2).choose 2 = (k + 2) * (k + 1) := by
      rw [two_mul_choose_two, show k + 2 - 1 = k + 1 by omega]
    omega
  -- Double the complete-graph edge count: 2·C(n,2) = (2k+3+c)(2k+2+c).
  have d2 : 2 * (2 * k + 3 + c).choose 2 = (2 * k + 3 + c) * (2 * k + 2 + c) := by
    rw [two_mul_choose_two, show 2 * k + 3 + c - 1 = 2 * k + 2 + c by omega]
  -- The doubled inequality is a manifestly nonnegative polynomial gap.
  have hle : 2 * edgeThreshold (2 * k + 3 + c) k ≤ 2 * (2 * k + 3 + c).choose 2 := by
    rw [d1, d2]; nlinarith [Nat.zero_le k, Nat.zero_le c, Nat.zero_le (k * c),
      Nat.zero_le (k * k)]
  omega

/-- **Exact surplus of the edge threshold below the complete graph.**  On the Woodall
    range `n ≥ 2k+3` the slack between the threshold and the total number of edges of
    `Kₙ` is the explicit closed form

        C(n, 2) = edgeThreshold n k + (k·(k+2) + (n − (2k+3))·(k+1)).

    This upgrades the inequality `edgeThreshold_le_choose_two` to an equality: the
    surplus `k(k+2) + (n−(2k+3))(k+1)` is a manifestly nonnegative polynomial that
    vanishes iff `k = 0` and `n = 2k+3` — the single degenerate point `edgeThreshold 3 0
    = C(3,2) = 3`.  Writing `c = n − (2k+3)`, halving the parent's doubled identity
    `2·edgeThreshold = (k+2+c)(k+1+c) + (k+2)(k+1) + 2` against `2·C(n,2) =
    (2k+3+c)(2k+2+c)` gives exactly this gap. -/
theorem edgeThreshold_add_surplus_eq_choose_two (n k : ℕ) (h : 2 * k + 3 ≤ n) :
    edgeThreshold n k + (k * (k + 2) + (n - (2 * k + 3)) * (k + 1)) = n.choose 2 := by
  obtain ⟨c, rfl⟩ : ∃ c, n = 2 * k + 3 + c := ⟨n - (2 * k + 3), by omega⟩
  have hc : 2 * k + 3 + c - (2 * k + 3) = c := by omega
  rw [hc]
  -- Double both sides: 2·edgeThreshold = (k+2+c)(k+1+c) + (k+2)(k+1) + 2.
  have d1 : 2 * edgeThreshold (2 * k + 3 + c) k
      = (k + 2 + c) * (k + 1 + c) + (k + 2) * (k + 1) + 2 := by
    unfold edgeThreshold
    have h1 : 2 * (2 * k + 3 + c - k - 1).choose 2 = (k + 2 + c) * (k + 1 + c) := by
      rw [show 2 * k + 3 + c - k - 1 = k + 2 + c by omega, two_mul_choose_two,
          show k + 2 + c - 1 = k + 1 + c by omega]
    have h2 : 2 * (k + 2).choose 2 = (k + 2) * (k + 1) := by
      rw [two_mul_choose_two, show k + 2 - 1 = k + 1 by omega]
    omega
  have d2 : 2 * (2 * k + 3 + c).choose 2 = (2 * k + 3 + c) * (2 * k + 2 + c) := by
    rw [two_mul_choose_two, show 2 * k + 3 + c - 1 = 2 * k + 2 + c by omega]
  -- The doubled identity is a polynomial equality; cancel the factor of 2.
  have key : 2 * (edgeThreshold (2 * k + 3 + c) k
      + (k * (k + 2) + c * (k + 1))) = 2 * (2 * k + 3 + c).choose 2 := by
    rw [Nat.mul_add, d1, d2]; ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) key

/-- **Strict non-degeneracy of the edge threshold.**  Away from the single degenerate
    point `(k, n) = (0, 3)`, the threshold is *strictly* below the complete-graph edge
    count: for `n ≥ 2k+3` with either `k ≥ 1` or `n > 2k+3`,

        edgeThreshold n k < C(n, 2).

    Hence there is genuine room above the threshold — the long-cycle hypothesis
    `edgeCount G ≥ edgeThreshold n k` is satisfied by strictly denser graphs than the
    threshold graph, and in particular is not forced to be the complete graph. -/
theorem edgeThreshold_lt_choose_two (n k : ℕ) (h : 2 * k + 3 ≤ n)
    (hnt : 1 ≤ k ∨ 2 * k + 3 < n) : edgeThreshold n k < n.choose 2 := by
  have hid := edgeThreshold_add_surplus_eq_choose_two n k h
  have hpos : 0 < k * (k + 2) + (n - (2 * k + 3)) * (k + 1) := by
    rcases hnt with hk | hn
    · have : 0 < k * (k + 2) := Nat.mul_pos hk (by omega)
      omega
    · have : 0 < (n - (2 * k + 3)) * (k + 1) := Nat.mul_pos (by omega) (by omega)
      omega
  omega

end Erdos1012OQ01OQ02
