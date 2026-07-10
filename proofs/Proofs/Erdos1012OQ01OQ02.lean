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

/-! ## Structural arithmetic in the clique size `k`

The results above vary the vertex count `n` with `k` fixed.  This section supplies the
complementary variation in `k` with `n` fixed.  Because `edgeThreshold n k =
C(n-k-1,2) + C(k+2,2) + 1` moves both binomial coefficients in opposite directions as
`k` grows (the first shrinks, the second grows), the discrete `k`-derivative is the
*signed* quantity `2k + 4 − n`:

    edgeThreshold n (k+1) − edgeThreshold n k = (k+2) − (n-k-2) = 2k + 4 − n     (for n ≥ k+2).

We record it as the subtraction-free `ℕ` identity `edgeThreshold n (k+1) + n =
edgeThreshold n k + (2k+4)` and read off the sign: the threshold is **U-shaped
(convex) in `k`**, decreasing while `n ≥ 2k+4` and increasing once `n ≤ 2k+4`, with
its minimum at `k ≈ (n-4)/2`.  This is the `k`-analogue of the well-defined-minimum
structure the parent needs to make `f(k)` meaningful. -/

/-- **Recurrence in `k`.**  For `n ≥ k+2`, incrementing the clique size satisfies the
    subtraction-free identity `edgeThreshold n (k+1) + n = edgeThreshold n k + (2k+4)`,
    i.e. the signed discrete `k`-derivative is `2k + 4 − n`.  Unlike the `n`-recurrence
    this derivative changes sign, so the identity is stated additively to stay in `ℕ`. -/
theorem edgeThreshold_succ_right (n k : ℕ) (h : k + 2 ≤ n) :
    edgeThreshold n (k + 1) + n = edgeThreshold n k + (2 * k + 4) := by
  unfold edgeThreshold
  have ha : n - k - 1 = (n - k - 2) + 1 := by omega
  have hb : n - (k + 1) - 1 = n - k - 2 := by omega
  have hc : k + 1 + 2 = (k + 2) + 1 := by omega
  rw [ha, hb, hc, choose_two_succ (n - k - 2), choose_two_succ (k + 2)]
  omega

/-- **Decreasing branch in `k`.**  While the graph is large relative to the clique size
    (`n ≥ 2k+4`), the threshold does not increase with `k`:
    `edgeThreshold n (k+1) ≤ edgeThreshold n k`. -/
theorem edgeThreshold_succ_right_le (n k : ℕ) (h : 2 * k + 4 ≤ n) :
    edgeThreshold n (k + 1) ≤ edgeThreshold n k := by
  have hrec := edgeThreshold_succ_right n k (by omega)
  omega

/-- **Increasing branch in `k`.**  Once the clique size is large relative to the graph
    (`k+2 ≤ n ≤ 2k+4`), the threshold does not decrease with `k`:
    `edgeThreshold n k ≤ edgeThreshold n (k+1)`.  Together with
    `edgeThreshold_succ_right_le` this shows the threshold is U-shaped (convex) in `k`,
    minimized near `k = (n-4)/2`. -/
theorem edgeThreshold_le_succ_right (n k : ℕ) (h1 : k + 2 ≤ n) (h2 : n ≤ 2 * k + 4) :
    edgeThreshold n k ≤ edgeThreshold n (k + 1) := by
  have hrec := edgeThreshold_succ_right n k h1
  omega

/-! ## Connecting the `n`-recurrence to the parent's boundary difference

The parent `Erdos1012OQ01.threshold_diff` records the jump across the Woodall boundary
`n = 2k+2 → 2k+3` abstractly, as the binomial difference `C(k+2,2) − C(k+1,2)`.  The
`n`-recurrence `edgeThreshold_succ_left` pins that single step down concretely: the
boundary sits at `n = 2k+2`, where the discrete `n`-derivative `n − k − 1` evaluates to
`k + 1`.  So the parent's boundary difference is *exactly* `k + 1`, and the two ways of
computing it agree. -/

/-- Pascal step for the second binomial coefficient: `C(k+2, 2) − C(k+1, 2) = k + 1`.
    This is the parent's abstract `threshold_diff` right-hand side, evaluated. -/
theorem choose_two_diff_succ (k : ℕ) :
    (k + 2).choose 2 - (k + 1).choose 2 = k + 1 := by
  have h : (k + 1 + 1).choose 2 = (k + 1).choose 2 + (k + 1) := choose_two_succ (k + 1)
  rw [show k + 1 + 1 = k + 2 by omega] at h
  omega

/-- **The Woodall boundary step.**  Crossing the boundary `n = 2k+2 → 2k+3` raises the
    threshold by exactly `k + 1` — the `n`-recurrence's discrete derivative `n − k − 1`
    evaluated at `n = 2k+2`. -/
theorem edgeThreshold_boundary_step (k : ℕ) :
    edgeThreshold (2 * k + 3) k = edgeThreshold (2 * k + 2) k + (k + 1) := by
  have h := edgeThreshold_succ_left (2 * k + 2) k (by omega)
  rw [show 2 * k + 2 + 1 = 2 * k + 3 by omega] at h
  omega

/-- **The parent's boundary difference, evaluated concretely.**  The Woodall-boundary
    jump `edgeThreshold (2k+3) k − edgeThreshold (2k+2) k` — which the parent
    `threshold_diff` expresses as `C(k+2,2) − C(k+1,2)` — is exactly `k + 1`.  This closes
    the loop between the abstract binomial difference and the `n`-recurrence: both routes
    give `k + 1` (cf. `choose_two_diff_succ`). -/
theorem threshold_diff_eq (k : ℕ) :
    edgeThreshold (2 * k + 3) k - edgeThreshold (2 * k + 2) k = k + 1 := by
  rw [edgeThreshold_boundary_step]; omega

/-! ## Quadratic (Θ(n²)) growth of the threshold

For fixed `k` the threshold grows quadratically in `n`.  Doubling it isolates the leading
term `(n-k-1)(n-k-2)`, and it is sandwiched between that quadratic below and
`n(n-1) = 2·C(n,2)` above — both degree-2 in `n` with leading coefficient 1.  So the
threshold grows like `½n²`, the same rate as the complete graph. -/

/-- Subtraction-free doubled form of the threshold for `n ≥ k+2`:
    `2·edgeThreshold n k = (n-k-1)(n-k-2) + (k+2)(k+1) + 2`. -/
theorem two_mul_edgeThreshold (n k : ℕ) (h : k + 2 ≤ n) :
    2 * edgeThreshold n k = (n - k - 1) * (n - k - 2) + (k + 2) * (k + 1) + 2 := by
  unfold edgeThreshold
  have h1 : 2 * (n - k - 1).choose 2 = (n - k - 1) * (n - k - 2) := by
    rw [two_mul_choose_two, show n - k - 1 - 1 = n - k - 2 by omega]
  have h2 : 2 * (k + 2).choose 2 = (k + 2) * (k + 1) := by
    rw [two_mul_choose_two, show k + 2 - 1 = k + 1 by omega]
  omega

/-- **Quadratic lower bound.**  For `n ≥ k+2`, the leading term already forces
    `(n-k-1)(n-k-2) ≤ 2·edgeThreshold n k`. -/
theorem edgeThreshold_quadratic_lower (n k : ℕ) (h : k + 2 ≤ n) :
    (n - k - 1) * (n - k - 2) ≤ 2 * edgeThreshold n k := by
  rw [two_mul_edgeThreshold n k h]; omega

/-- **Θ(n²) growth sandwich.**  For fixed `k` and `n ≥ 2k+3`, the doubled threshold is
    trapped between two quadratics in `n`:

        (n-k-1)(n-k-2) ≤ 2·edgeThreshold n k ≤ n(n-1) = 2·C(n,2).

    Both bounds are degree-2 in `n` with leading coefficient 1, so `edgeThreshold n k`
    grows like `½n²` — the same asymptotic rate as the complete-graph edge count `C(n,2)`,
    confirming the threshold is a genuinely quadratic (not vacuous, not linear) barrier. -/
theorem edgeThreshold_quadratic_sandwich (n k : ℕ) (h : 2 * k + 3 ≤ n) :
    (n - k - 1) * (n - k - 2) ≤ 2 * edgeThreshold n k ∧
      2 * edgeThreshold n k ≤ n * (n - 1) := by
  refine ⟨edgeThreshold_quadratic_lower n k (by omega), ?_⟩
  have hle := edgeThreshold_le_choose_two n k h
  have hd : 2 * n.choose 2 = n * (n - 1) := two_mul_choose_two n
  omega

/-! ## Discrete convexity: the second differences are constant

The first-difference results (`edgeThreshold_succ_left`, `edgeThreshold_succ_right`) have
discrete derivatives `n − k − 1` (in `n`) and `2k + 4 − n` (in `k`) that are themselves
*linear*, so the threshold is discretely **convex** in each variable: the second difference
is a strictly positive constant — `+1` in `n` and `+2` in `k`.  These identities upgrade the
monotone `n`-growth and the two U-shaped `k`-branches to a quantitative convexity statement:
a positive second difference forces the `k`-profile to be strictly convex (hence a unique
minimizing band, sharpening `edgeThreshold_succ_right_le` / `edgeThreshold_le_succ_right`)
and shows the `n`-growth is genuinely accelerating (consistent with the `Θ(n²)` sandwich). -/

/-- **Discrete convexity in `n`: the second difference is the constant `+1`.**  For
    `n ≥ k+1`,
    `edgeThreshold (n+2) k + edgeThreshold n k = 2·edgeThreshold (n+1) k + 1`.
    The `n`-derivative `n − k − 1` (`edgeThreshold_succ_left`) increases by exactly `1`
    with each added vertex, so the threshold is strictly convex in `n`. -/
theorem edgeThreshold_second_diff_left (n k : ℕ) (h : k + 1 ≤ n) :
    edgeThreshold (n + 2) k + edgeThreshold n k = 2 * edgeThreshold (n + 1) k + 1 := by
  have h1 := edgeThreshold_succ_left n k h
  have h2 := edgeThreshold_succ_left (n + 1) k (by omega)
  rw [show n + 1 + 1 = n + 2 by omega, show n + 1 - k - 1 = n - k by omega] at h2
  omega

/-- **Discrete convexity in `k`: the second difference is the constant `+2`.**  For
    `n ≥ k+3`,
    `edgeThreshold n (k+2) + edgeThreshold n k = 2·edgeThreshold n (k+1) + 2`.
    The signed `k`-derivative `2k + 4 − n` (`edgeThreshold_succ_right`) increases by exactly
    `2` per unit of `k`, so the threshold is strictly convex in `k` — pinning the U-shape to
    a unique minimizing band near `k = (n-4)/2`. -/
theorem edgeThreshold_second_diff_right (n k : ℕ) (h : k + 3 ≤ n) :
    edgeThreshold n (k + 2) + edgeThreshold n k = 2 * edgeThreshold n (k + 1) + 2 := by
  have h1 := edgeThreshold_succ_right n k (by omega)
  have h2 := edgeThreshold_succ_right n (k + 1) (by omega)
  rw [show k + 1 + 1 = k + 2 by omega] at h2
  omega

/-! ## The `k`-profile has a global minimum (a well-defined `f(k)` minimizer)

The single-step branch lemmas `edgeThreshold_succ_right_le` (decreasing while `n ≥ 2k+4`)
and `edgeThreshold_le_succ_right` (increasing while `n ≤ 2k+4`) only compare *adjacent*
clique sizes.  Iterating each along its branch gives genuine range-monotonicity — the
threshold is antitone up to the turning point and monotone after it — and the two chains
meet at the parity-uniform minimizer `k₀ = ⌊(n-3)/2⌋`, giving a *global* lower bound
`edgeThreshold n k₀ ≤ edgeThreshold n k` for every clique size `k`.  This is precisely the
"well-defined minimum" structure that makes the Woodall function `f(k)` meaningful: the
edge threshold, viewed as a function of `k`, is minimized at one location. -/

/-- **Antitone chain on the decreasing branch.**  Iterating `edgeThreshold_succ_right_le`:
    whenever `k ≤ j` and the whole run stays in the decreasing region (`2j+2 ≤ n`, the
    binding constraint at the top step `j-1 → j`), the threshold has fallen:
    `edgeThreshold n j ≤ edgeThreshold n k`. -/
theorem edgeThreshold_antitone_left (n : ℕ) {k j : ℕ} (hkj : k ≤ j)
    (h : 2 * j + 2 ≤ n) : edgeThreshold n j ≤ edgeThreshold n k := by
  revert h
  induction j, hkj using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ j hkj ih =>
    intro h
    exact le_trans (edgeThreshold_succ_right_le n j (by omega)) (ih (by omega))

/-- **Monotone chain on the increasing branch.**  Iterating `edgeThreshold_le_succ_right`:
    whenever `k ≤ j`, the run starts in the increasing region (`n ≤ 2k+4`, binding at the
    bottom step) and the top index stays meaningful (`j+1 ≤ n`, binding at `j-1 → j`), the
    threshold has risen: `edgeThreshold n k ≤ edgeThreshold n j`. -/
theorem edgeThreshold_monotone_right (n : ℕ) {k j : ℕ} (hkj : k ≤ j)
    (h1 : n ≤ 2 * k + 4) (h2 : j + 1 ≤ n) :
    edgeThreshold n k ≤ edgeThreshold n j := by
  revert h2
  induction j, hkj using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ j hkj ih =>
    intro h2
    have step : edgeThreshold n j ≤ edgeThreshold n (j + 1) :=
      edgeThreshold_le_succ_right n j (by omega) (by omega)
    exact le_trans (ih (by omega)) step

/-- **Global minimum of the `k`-profile.**  For `n ≥ 5` the threshold, as a function of the
    clique size `k`, attains its minimum at the parity-uniform location
    `k₀ = ⌊(n-3)/2⌋`: for *every* clique size `k` with `k+2 ≤ n`,

        edgeThreshold n k₀ ≤ edgeThreshold n k.

    The choice `k₀ = ⌊(n-3)/2⌋` handles both parities at once — for even `n` it is the
    turning point `(n-4)/2` (where `2k₀+4 = n`), and for odd `n` it is `(n-3)/2` (where
    `2k₀+2 = n-1` and `2k₀+4 = n+1`), each side of it strictly monotone.  Seeds `k ≤ k₀`
    are handled by the antitone chain (decreasing branch), seeds `k > k₀` by the monotone
    chain (increasing branch); the branch constraints `2k₀+2 ≤ n` and `n ≤ 2k₀+4` both hold
    for this `k₀`.  This upgrades the qualitative "U-shaped in `k`" observation to a proven
    single global minimizer — the well-defined minimum underlying `f(k)`. -/
theorem edgeThreshold_min_at (n : ℕ) (hn : 5 ≤ n) {k : ℕ} (hk : k + 2 ≤ n) :
    edgeThreshold n ((n - 3) / 2) ≤ edgeThreshold n k := by
  rcases le_or_lt k ((n - 3) / 2) with hle | hlt
  · exact edgeThreshold_antitone_left n hle (by omega)
  · exact edgeThreshold_monotone_right n (le_of_lt hlt) (by omega) (by omega)

/-! ## Strict convexity: the minimizing band and a *unique* minimizer for odd `n`

The `k`-profile results above are all weak (`≤`): the branch lemmas
`edgeThreshold_succ_right_le` / `edgeThreshold_le_succ_right` and the global bound
`edgeThreshold_min_at` only certify `edgeThreshold n k₀ ≤ edgeThreshold n k`.  Yet the
docstring for this section calls the profile *strictly convex* with a *single* global
minimizer — a claim the second-difference identity `edgeThreshold_second_diff_right`
(constant `+2`) supports but which the weak lemmas do not yet witness.  This section
supplies the missing strictness.

The signed `k`-derivative is `2k + 4 − n` (`edgeThreshold_succ_right`), so a single step
`k → k+1` is:

* strictly *decreasing* once `n ≥ 2k+5` (past the turning point),
* *flat* exactly at `n = 2k+4` (even `n`, giving a width-2 minimizing band), and
* strictly *increasing* while `n ≤ 2k+3` (before the turning point).

Iterating the two strict steps yields strict chains, and hence a strict global minimum
for **odd** `n` — where no flat turning point exists, the minimizer `k₀ = (n-3)/2` is
unique.  (For even `n` the minimum is genuinely attained on the adjacent pair
`{k₀, k₀+1}`, recorded by `edgeThreshold_flat_at_turning`, so a unique minimizer is a
strictly odd-`n` phenomenon.) -/

/-- **Flat bottom of the `k`-profile (even `n`).**  At the exact turning point `n = 2k+4`
    the signed `k`-derivative `2k+4−n` vanishes, so two adjacent clique sizes give the
    *same* threshold: `edgeThreshold n k = edgeThreshold n (k+1)`.  This is why for even
    `n` the global minimum `edgeThreshold_min_at` is attained on the adjacent pair
    `{k₀, k₀+1}` — a width-2 flat band rather than a single point. -/
theorem edgeThreshold_flat_at_turning (n k : ℕ) (h : n = 2 * k + 4) :
    edgeThreshold n k = edgeThreshold n (k + 1) := by
  have hrec := edgeThreshold_succ_right n k (by omega)
  omega

/-- **Strictly decreasing branch in `k`.**  Strengthening `edgeThreshold_succ_right_le`
    from `≤` to `<`: once `n ≥ 2k+5` (strictly past the turning point) the threshold
    strictly falls, `edgeThreshold n (k+1) < edgeThreshold n k`. -/
theorem edgeThreshold_succ_right_lt (n k : ℕ) (h : 2 * k + 5 ≤ n) :
    edgeThreshold n (k + 1) < edgeThreshold n k := by
  have hrec := edgeThreshold_succ_right n k (by omega)
  omega

/-- **Strictly increasing branch in `k`.**  Strengthening `edgeThreshold_le_succ_right`
    from `≤` to `<`: while `k+2 ≤ n ≤ 2k+3` (strictly before the turning point) the
    threshold strictly rises, `edgeThreshold n k < edgeThreshold n (k+1)`. -/
theorem edgeThreshold_lt_succ_right_strict (n k : ℕ) (h1 : k + 2 ≤ n) (h2 : n ≤ 2 * k + 3) :
    edgeThreshold n k < edgeThreshold n (k + 1) := by
  have hrec := edgeThreshold_succ_right n k h1
  omega

/-- **Strictly antitone chain on the decreasing branch.**  Strengthening
    `edgeThreshold_antitone_left`: whenever `k < j` and the top step `j-1 → j` is strictly
    past the turning point (`2j+3 ≤ n`), the threshold has *strictly* fallen:
    `edgeThreshold n j < edgeThreshold n k`.  (The top step is strict by
    `edgeThreshold_succ_right_lt`; the remainder is covered by the weak chain.) -/
theorem edgeThreshold_antitone_left_strict (n : ℕ) {k j : ℕ} (hkj : k < j)
    (h : 2 * j + 3 ≤ n) : edgeThreshold n j < edgeThreshold n k := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hstep : edgeThreshold n (j' + 1) < edgeThreshold n j' :=
    edgeThreshold_succ_right_lt n j' (by omega)
  exact lt_of_lt_of_le hstep (edgeThreshold_antitone_left n (by omega) (by omega))

/-- **Strictly monotone chain on the increasing branch.**  Strengthening
    `edgeThreshold_monotone_right`: whenever `k < j`, the bottom step `k → k+1` is strictly
    before the turning point (`n ≤ 2k+3`) and the top index stays meaningful (`j+1 ≤ n`),
    the threshold has *strictly* risen: `edgeThreshold n k < edgeThreshold n j`. -/
theorem edgeThreshold_monotone_right_strict (n : ℕ) {k j : ℕ} (hkj : k < j)
    (h1 : n ≤ 2 * k + 3) (h2 : j + 1 ≤ n) :
    edgeThreshold n k < edgeThreshold n j := by
  have hstep : edgeThreshold n k < edgeThreshold n (k + 1) :=
    edgeThreshold_lt_succ_right_strict n k (by omega) h1
  exact lt_of_lt_of_le hstep (edgeThreshold_monotone_right n (by omega) (by omega) h2)

/-- **Unique global minimizer of the `k`-profile for odd `n`.**  When `n` is odd (`n ≥ 5`)
    there is no flat turning point (`n = 2k+4` has no integer solution), so the minimizer
    `k₀ = (n-3)/2` is the *strict* global minimum: for every other clique size `k` with
    `k+2 ≤ n` and `k ≠ k₀`,

        edgeThreshold n k₀ < edgeThreshold n k.

    Seeds `k < k₀` fall on the strictly decreasing branch (via
    `edgeThreshold_antitone_left_strict`, whose top-step constraint `2k₀+3 = n` is met with
    equality); seeds `k > k₀` fall on the strictly increasing branch (via
    `edgeThreshold_monotone_right_strict`, whose bottom-step constraint `n ≤ 2k₀+3 = n` is
    likewise tight).  This upgrades the weak `edgeThreshold_min_at` to a genuinely unique
    minimizer — the sharpest form of the "well-defined minimum" underlying `f(k)`. -/
theorem edgeThreshold_min_at_unique_odd (n : ℕ) (hn : 5 ≤ n) (hodd : Odd n) {k : ℕ}
    (hk : k + 2 ≤ n) (hne : k ≠ (n - 3) / 2) :
    edgeThreshold n ((n - 3) / 2) < edgeThreshold n k := by
  obtain ⟨m, rfl⟩ := hodd
  have hk0 : (2 * m + 1 - 3) / 2 = m - 1 := by omega
  rw [hk0] at hne ⊢
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- k < k₀ = m-1: strictly decreasing branch, upper index m-1 with 2(m-1)+3 = n
    exact edgeThreshold_antitone_left_strict n hlt (by omega)
  · -- k > k₀ = m-1: strictly increasing branch, bottom index m-1 with n ≤ 2(m-1)+3
    exact edgeThreshold_monotone_right_strict n hgt (by omega) (by omega)

end Erdos1012OQ01OQ02
