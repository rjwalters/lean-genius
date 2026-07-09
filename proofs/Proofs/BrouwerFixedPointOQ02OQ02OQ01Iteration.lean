import Mathlib
import Proofs.BrouwerFixedPointOQ02OQ02OQ01

/-
# Brouwer Fixed Point — OQ-02-OQ-02-OQ-01: multi-step iteration bounds

The base entry `BrouwerFixedPointOQ02OQ02OQ01.lean` establishes the single-step
geometric decay (`iterate_dist`) and the a priori / a posteriori error estimates
(`apriori_estimate`, `aposteriori_estimate`), together with the two-map composition
law (`contraction_comp`).  What it leaves for later ("Convergence/existence … the
iterates converge"; "turn the a priori estimate into an explicit query count";
"iterating m maps") is the *asymptotic* consequence of those bounds.  This file
supplies it, purely from the abstract contraction hypothesis
`∀ x y, |f x − f y| ≤ L·|x − y|`.

  * `iterate_contraction`         — the m-fold iterate `f^[m]` is an `Lᵐ`-contraction:
    `|f^[m] x − f^[m] y| ≤ Lᵐ·|x − y|`.  (The "iterating m maps" step, specialised to
    iterating a single contraction; generalises `contraction_comp` from 2 to m maps.)
  * `iterate_dist_tendsto`        — for `0 ≤ L < 1`, the two-point spread of the
    iterates collapses geometrically: `|f^[m] x − f^[m] y| → 0`.
  * `apriori_iteration_count`     — **convergence with a computable stopping rule.**
    From the a priori bound `|xₙ − x*| ≤ Lⁿ/(1−L)·|x₁ − x₀|`, for every target
    accuracy `ε > 0` there is an iteration count `N` past which `|xₙ − x*| ≤ ε`.
    This is the qualitative content of the parent's `O(log 1/ε)` iteration bound:
    finitely many steps of fixed-point iteration reach any prescribed accuracy.
  * `iteration_converges`         — restatement as `xₙ → x*` in ℝ.

All results are fully machine-checked (0 axioms, 0 sorries).

Reference: Banach (1922); the base entry `BrouwerFixedPointOQ02OQ02OQ01.lean`.
-/

namespace BrouwerOQ02OQ02OQ01Iteration

open Filter Topology
open BrouwerOQ02OQ02OQ01

/-- **The m-fold iterate of an `L`-contraction is an `Lᵐ`-contraction.**  Iterating a
    single contraction `f` (constant `L ≥ 0`) `m` times contracts distances by `Lᵐ`:
    `|f^[m] x − f^[m] y| ≤ Lᵐ·|x − y|`.  This is the "iterating m maps" step for a
    repeated map; combined with `0 ≤ L < 1` it makes `f^[m]` an ever-sharper
    contraction, the engine behind convergence of fixed-point iteration. -/
theorem iterate_contraction (f : ℝ → ℝ) (L : ℝ) (hL0 : 0 ≤ L)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|) (m : ℕ) (x y : ℝ) :
    |f^[m] x - f^[m] y| ≤ L ^ m * |x - y| := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ', Function.comp_apply, Function.comp_apply]
    calc |f (f^[m] x) - f (f^[m] y)| ≤ L * |f^[m] x - f^[m] y| := hf _ _
      _ ≤ L * (L ^ m * |x - y|) := mul_le_mul_of_nonneg_left ih hL0
      _ = L ^ (m + 1) * |x - y| := by ring

/-- **Geometric collapse of the iterates' spread.**  For a contraction with
    `0 ≤ L < 1`, the distance between the `m`-fold iterates of any two starting points
    tends to `0`: `|f^[m] x − f^[m] y| → 0` as `m → ∞`.  This is the two-point form of
    convergence; taking `y` a fixed point specialises it to error decay. -/
theorem iterate_dist_tendsto (f : ℝ → ℝ) (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L < 1)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|) (x y : ℝ) :
    Tendsto (fun m => |f^[m] x - f^[m] y|) atTop (𝓝 0) := by
  -- squeeze between 0 and the vanishing bound Lᵐ·|x − y|
  have hbound : Tendsto (fun m : ℕ => L ^ m * |x - y|) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hL0 hL1).mul_const |x - y|
    simpa using h
  refine squeeze_zero (fun m => abs_nonneg _) (fun m => ?_) hbound
  exact iterate_contraction f L hL0 hf m x y

/-- **Convergence with a computable stopping rule.**  Under the fixed-point iteration
    `xₙ₊₁ = f xₙ` of an `L`-contraction (`0 ≤ L < 1`) with fixed point `x*`, every
    target accuracy `ε > 0` is reached after finitely many steps: there is an iteration
    count `N` with `|xₙ − x*| ≤ ε` for all `n ≥ N`.  This turns the a priori bound
    `|xₙ − x*| ≤ Lⁿ/(1−L)·|x₁ − x₀|` into the parent's `O(log 1/ε)` guarantee — the
    number of iterations needed for accuracy `ε` is finite (and bounded before iterating,
    since the whole bound is expressed through the first increment `|x₁ − x₀|`). -/
theorem apriori_iteration_count (f : ℝ → ℝ) (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L < 1)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (x : ℕ → ℝ) (hx : ∀ n, x (n + 1) = f (x n))
    (xstar : ℝ) (hfp : f xstar = xstar) (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, |x n - xstar| ≤ ε := by
  have hcontr : (0 : ℝ) < 1 - L := by linarith
  -- the a priori bound sequence tends to 0 …
  have htend : Tendsto (fun n : ℕ => L ^ n / (1 - L) * |x 1 - x 0|) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hL0 hL1).mul_const
      (|x 1 - x 0| / (1 - L))
    rw [zero_mul] at h
    exact h.congr (fun n => by ring)
  -- … so it is eventually below ε …
  have hev : ∀ᶠ n in atTop, L ^ n / (1 - L) * |x 1 - x 0| ≤ ε := by
    have hlt : ∀ᶠ n in atTop, L ^ n / (1 - L) * |x 1 - x 0| ∈ Set.Iio ε :=
      htend.eventually (Iio_mem_nhds hε)
    filter_upwards [hlt] with n hn using le_of_lt hn
  -- … and the a priori estimate dominates the actual error.
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun n hn => ?_⟩
  exact le_trans (apriori_estimate f L hL0 hL1 hf x hx xstar hfp n) (hN n hn)

/-- **Fixed-point iteration converges to the fixed point.**  Restatement of
    `apriori_iteration_count` as a limit: `xₙ → x*`. -/
theorem iteration_converges (f : ℝ → ℝ) (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L < 1)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (x : ℕ → ℝ) (hx : ∀ n, x (n + 1) = f (x n))
    (xstar : ℝ) (hfp : f xstar = xstar) :
    Tendsto x atTop (𝓝 xstar) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hg : Tendsto (fun n : ℕ => L ^ n / (1 - L) * |x 1 - x 0|) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hL0 hL1).mul_const
      (|x 1 - x 0| / (1 - L))
    rw [zero_mul] at h
    exact h.congr (fun n => by ring)
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hg
  rw [Real.dist_eq]
  exact apriori_estimate f L hL0 hL1 hf x hx xstar hfp n

end BrouwerOQ02OQ02OQ01Iteration
