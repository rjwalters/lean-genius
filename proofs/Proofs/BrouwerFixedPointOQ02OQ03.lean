/-
  Newton's Method: Quadratic Convergence Near a Simple Root

  Open Question OQ-02-OQ-03 (from BrouwerFixedPointOQ02):
  Prove Newton's method has quadratic convergence rate for smooth functions.

  **Result**: If f : ℝ → ℝ is C² near a simple root x* (f(x*) = 0, f'(x*) ≠ 0),
  then the Newton iteration xₙ₊₁ = xₙ - f(xₙ)/f'(xₙ) satisfies:
      |xₙ₊₁ - x*| ≤ C · |xₙ - x*|²
  for C = M/(2m), where M bounds |f''| and m bounds |f'| from below near x*.

  **Mathematical Structure** (Taylor remainder → algebraic identity):

  From the second-order Taylor expansion around xₙ:
    f(x*) = f(xₙ) + f'(xₙ)(x* - xₙ) + f''(ξ)/2 · (x* - xₙ)²   (Taylor)

  Since f(x*) = 0:
    -f(xₙ)/f'(xₙ) = (x* - xₙ) + f''(ξ)/(2f'(xₙ)) · (x* - xₙ)²

  Adding xₙ - x* to both sides:
    xₙ₊₁ - x* = (xₙ - f(xₙ)/f'(xₙ)) - x* = f''(ξ)/(2f'(xₙ)) · (x* - xₙ)²

  Bounding: |xₙ₊₁ - x*| ≤ |f''(ξ)|/(2|f'(xₙ)|) · |xₙ - x*|² ≤ M/(2m) · |xₙ - x*|²

  The quadratic factor explains why Newton's method doubles the number of
  correct decimal digits at each step (when it converges).

  **Status**: 0 sorries, 0 axioms (fully machine-checked).
  The main result (one-step bound) is fully proved from an explicit ξ hypothesis.
  A second theorem uses Mathlib's Taylor theorem to get ξ for C² functions, and
  `newton_convergence_rate` proves the full doubling-exponent rate |xₙ - x*| ≤
  ε·(C·ε)^(2ⁿ - 1) inside the Newton basin (C + 1)·ε ≤ 1.

  See BrouwerFixedPointOQ02.lean for the parent (computational fixed-point complexity).
-/

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

open Set Real Filter

namespace NewtonMethod

/-! ## Core Definitions -/

/-- The Newton iteration step: x ↦ x - f(x)/f'(x). -/
noncomputable def newtonStep (f f' : ℝ → ℝ) (x : ℝ) : ℝ := x - f x / f' x

/-- Iterate Newton's method n times. -/
noncomputable def newtonIter (f f' : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0,     x => x
  | n + 1, x => newtonStep f f' (newtonIter f f' n x)

/-! ## Main Theorem: One-Step Quadratic Error Bound -/

/-- **Newton's Quadratic Convergence** (one step):
    Given a C² function f with simple root x*, one Newton step satisfies:
      |newton(x₀) - x*| ≤ M/(2m) · |x₀ - x*|²

    The proof uses the second-order Taylor remainder: the Newton error equals
    exactly f''(ξ)/(2f'(x₀)) · (x* - x₀)² for some ξ between x₀ and x*.

    Hypotheses:
    - `hf_root`: x* is a root of f
    - `hf'_nz`: f'(x₀) ≠ 0 (guaranteed near x* by continuity when f'(x*) ≠ 0)
    - `htaylor`: the Taylor remainder identity holds for some ξ (Lagrange remainder)
    - `hf''`: |f''(ξ)| is bounded by M ≥ 0
    - `hf'`: |f'(x₀)| ≥ m > 0 (lower bound on derivative) -/
theorem newton_step_quadratic_bound
    {f f'' : ℝ → ℝ} {f' : ℝ → ℝ}
    {x_star x₀ : ℝ}
    (hf_root : f x_star = 0)
    (hf'_nz : f' x₀ ≠ 0)
    -- Taylor: f(x*) = f(x₀) + f'(x₀)(x* - x₀) + f''(ξ)/2 · (x* - x₀)² for some ξ
    {ξ : ℝ}
    (htaylor : f x_star = f x₀ + f' x₀ * (x_star - x₀) + f'' ξ * (x_star - x₀) ^ 2 / 2)
    -- Bound on second derivative at ξ
    {M : ℝ} (hM : 0 ≤ M) (hf'' : |f'' ξ| ≤ M)
    -- Lower bound on first derivative at x₀
    {m : ℝ} (hm : 0 < m) (hf' : m ≤ |f' x₀|) :
    |newtonStep f f' x₀ - x_star| ≤ M / (2 * m) * |x₀ - x_star| ^ 2 := by
  -- Step 1: Show the Newton error equals f''(ξ)/(2f'(x₀)) · (x* - x₀)²
  have hfx₀ : f x₀ = -f' x₀ * (x_star - x₀) - f'' ξ / 2 * (x_star - x₀) ^ 2 := by
    have h := htaylor; rw [hf_root] at h; linarith
  have heq : newtonStep f f' x₀ - x_star = f'' ξ / (2 * f' x₀) * (x_star - x₀) ^ 2 := by
    simp only [newtonStep]
    field_simp [hf'_nz]
    linarith [hfx₀]
  -- Step 2: Bound |error| ≤ |f''(ξ)| / (2|f'(x₀)|) · |x₀ - x*|²
  rw [heq, abs_mul, abs_div]
  -- `|(x* - x₀)²| = |x₀ - x*|²` since squares are nonnegative and `|·|` is symmetric.
  have hsq : |(x_star - x₀) ^ 2| = |x₀ - x_star| ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs, abs_sub_comm]
  rw [hsq, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  -- Goal: |f''(ξ)| / (2 * |f'(x₀)|) * |x₀ - x*|² ≤ M / (2 * m) * |x₀ - x*|²
  -- `gcongr` reduces to `|f''(ξ)| ≤ M` and `2 * m ≤ 2 * |f'(x₀)|`, both discharged from
  -- the hypotheses `hf''` and `hf'` already in context.
  gcongr

/-! ## Applying Mathlib's Taylor Theorem to Get ξ -/

/-- **Taylor remainder existence** for C² functions:
    For a twice-continuously-differentiable function and x₀ < x*, there exists
    ξ ∈ (x₀, x*) such that the Lagrange remainder holds.
    This is `taylor_mean_remainder_lagrange` from Mathlib for n=1. -/
theorem taylor_remainder_exists {f : ℝ → ℝ} {x₀ x_star : ℝ} (hlt : x₀ < x_star)
    (hf_diff : ContDiffOn ℝ 1 f (Icc x₀ x_star))
    (hf'_diff : DifferentiableOn ℝ (iteratedDerivWithin 1 f (Icc x₀ x_star)) (Ioo x₀ x_star)) :
    ∃ ξ ∈ Ioo x₀ x_star,
      f x_star - (f x₀ + iteratedDerivWithin 1 f (Icc x₀ x_star) x₀ * (x_star - x₀)) =
      iteratedDerivWithin 2 f (Icc x₀ x_star) ξ * (x_star - x₀) ^ 2 / 2 := by
  -- Use Mathlib's taylor_mean_remainder_lagrange with n = 1 forced as a literal, so the
  -- Taylor polynomial and remainder appear as `taylorWithinEval f 1` / `iteratedDerivWithin 2`
  -- (avoiding an elaboration mismatch between `1` and `One.one`).
  obtain ⟨ξ, hξ, hrem⟩ :=
    @taylor_mean_remainder_lagrange f x_star x₀ 1 hlt hf_diff hf'_diff
  refine ⟨ξ, hξ, ?_⟩
  -- `taylorWithinEval f 1` is the order-1 Taylor polynomial `f(x₀) + f'(x₀)(x - x₀)`.
  have htw : taylorWithinEval f 1 (Icc x₀ x_star) x₀ x_star =
      f x₀ + iteratedDerivWithin 1 f (Icc x₀ x_star) x₀ * (x_star - x₀) := by
    rw [taylor_within_apply]
    simp [Finset.sum_range_succ, iteratedDerivWithin_zero, smul_eq_mul, Nat.factorial]
    ring
  rw [← htw, hrem]
  norm_num [Nat.factorial]

/-! ## Quadratic Convergence with C² Assumptions -/

/-- **Newton quadratic convergence for C² functions** (x₀ < x*):
    When f is C² on [x₀, x*], f(x*) = 0, and |f'(x₀)| ≥ m > 0,
    the Newton error satisfies the quadratic bound. -/
theorem newton_step_C2_bound
    {f : ℝ → ℝ} {x_star x₀ : ℝ}
    (hlt : x₀ < x_star)
    (hf_root : f x_star = 0)
    (hf_C2 : ContDiffOn ℝ 2 f (Icc x₀ x_star))
    -- Derivative f' at x₀ (using one-sided derivative for interval)
    (hf'_val : HasDerivWithinAt f (iteratedDerivWithin 1 f (Icc x₀ x_star) x₀) (Icc x₀ x_star) x₀)
    -- f'(x₀) ≠ 0 at the iterate
    (hf'_nz : iteratedDerivWithin 1 f (Icc x₀ x_star) x₀ ≠ 0)
    -- Bound M on |f''| on [x₀, x*]
    {M m : ℝ} (hM : 0 ≤ M) (hm : 0 < m)
    (hf''_bnd : ∀ x ∈ Icc x₀ x_star,
        |iteratedDerivWithin 2 f (Icc x₀ x_star) x| ≤ M)
    (hf'_low : m ≤ |iteratedDerivWithin 1 f (Icc x₀ x_star) x₀|) :
    |newtonStep f (fun x => iteratedDerivWithin 1 f (Icc x₀ x_star) x) x₀ - x_star|
      ≤ M / (2 * m) * |x₀ - x_star| ^ 2 := by
  -- Get the Taylor remainder ξ
  have hf_C1 : ContDiffOn ℝ 1 f (Icc x₀ x_star) := hf_C2.of_le (by norm_num)
  have hf'_cont : ContinuousOn (iteratedDerivWithin 1 f (Icc x₀ x_star)) (Icc x₀ x_star) := by
    exact (hf_C2.continuousOn_iteratedDerivWithin (by norm_num) (uniqueDiffOn_Icc hlt))
  have hf'_diff : DifferentiableOn ℝ (iteratedDerivWithin 1 f (Icc x₀ x_star)) (Ioo x₀ x_star) :=
    (hf_C2.differentiableOn_iteratedDerivWithin (by norm_num) (uniqueDiffOn_Icc hlt)).mono
      Ioo_subset_Icc_self
  obtain ⟨ξ, hξ, hrem⟩ := taylor_remainder_exists hlt hf_C1 hf'_diff
  -- Reformulate Taylor remainder as: f x_star = f x₀ + f'(x₀)(x* - x₀) + f''(ξ)/2 · (x*-x₀)²
  have htaylor : f x_star = f x₀ + iteratedDerivWithin 1 f (Icc x₀ x_star) x₀ * (x_star - x₀) +
      iteratedDerivWithin 2 f (Icc x₀ x_star) ξ * (x_star - x₀) ^ 2 / 2 := by
    linarith [hrem]
  apply newton_step_quadratic_bound hf_root hf'_nz htaylor hM
      (hf''_bnd ξ (Ioo_subset_Icc_self hξ)) hm hf'_low

/-! ## Iterated Convergence -/

/-- Contraction ratio for Newton's method: C = M / (2 * m). -/
noncomputable def newtonConstant (M m : ℝ) : ℝ := M / (2 * m)

/-- **Newton basin quadratic-convergence rate.**  If the one-step quadratic bound holds with
    constant `C` (whenever the current iterate is within `1/(C+1)` of the root), and the initial
    error is at most `ε` inside the Newton basin `(C + 1)·ε ≤ 1`, then the `n`-th iterate satisfies
      `|xₙ - x*| ≤ ε · (C·ε)^{2ⁿ - 1}`,
    the doubling-exponent hallmark of quadratic convergence.

    The basin hypothesis `(C + 1)·ε ≤ 1` (equivalently `ε ≤ 1/(C+1)`) is the correct precondition:
    the weaker `C·ε < 1` is insufficient because each application of `hstep` needs
    `|xₙ - x*| ≤ 1/(C+1)`, and only `(C + 1)·ε ≤ 1` guarantees that from the inductive bound. -/
theorem newton_convergence_rate
    {f f' : ℝ → ℝ} {x_star x₀ : ℝ}
    {C : ℝ} (hC : 0 ≤ C)
    -- Each step satisfies the quadratic bound with the SAME constant C
    (hstep : ∀ n, |newtonIter f f' n x₀ - x_star|
      ≤ 1 / (C + 1) →
      |newtonStep f f' (newtonIter f f' n x₀) - x_star|
      ≤ C * |newtonIter f f' n x₀ - x_star| ^ 2)
    {ε : ℝ} (hε : 0 < ε) (hε1 : (C + 1) * ε ≤ 1)
    (h0 : |x₀ - x_star| ≤ ε) :
    ∀ n, |newtonIter f f' n x₀ - x_star| ≤ ε * (C * ε) ^ (2^n - 1) := by
  -- Basic facts about the contraction factor `C·ε ∈ [0, 1]`.
  have hCε0 : 0 ≤ C * ε := mul_nonneg hC hε.le
  have hCε1 : C * ε ≤ 1 := by nlinarith [hε.le]
  intro n
  induction n with
  | zero => simpa [newtonIter] using h0
  | succ n ih =>
    -- The inductive bound already keeps the iterate inside the basin `1/(C+1)`.
    have hpow_le_one : (C * ε) ^ (2 ^ n - 1) ≤ 1 := by
      calc (C * ε) ^ (2 ^ n - 1) ≤ 1 ^ (2 ^ n - 1) := pow_le_pow_left₀ hCε0 hCε1 _
        _ = 1 := one_pow _
    have hbasin : ε * (C * ε) ^ (2 ^ n - 1) ≤ 1 / (C + 1) := by
      have hεbasin : ε ≤ 1 / (C + 1) := by
        rw [le_div_iff₀ (by linarith)]; linarith [hε1]
      calc ε * (C * ε) ^ (2 ^ n - 1) ≤ ε * 1 := by
            exact mul_le_mul_of_nonneg_left hpow_le_one hε.le
        _ = ε := mul_one ε
        _ ≤ 1 / (C + 1) := hεbasin
    -- Apply the one-step bound at the `n`-th iterate.
    have hstep_n := hstep n (ih.trans hbasin)
    have hsucc : |newtonIter f f' (n + 1) x₀ - x_star|
        ≤ C * |newtonIter f f' n x₀ - x_star| ^ 2 := by
      rw [newtonIter]; exact hstep_n
    -- Square the inductive bound and simplify the exponent `2·(2ⁿ - 1) + 1 = 2^{n+1} - 1`.
    have hsq : |newtonIter f f' n x₀ - x_star| ^ 2 ≤ (ε * (C * ε) ^ (2 ^ n - 1)) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) ih 2
    calc |newtonIter f f' (n + 1) x₀ - x_star|
        ≤ C * |newtonIter f f' n x₀ - x_star| ^ 2 := hsucc
      _ ≤ C * (ε * (C * ε) ^ (2 ^ n - 1)) ^ 2 := mul_le_mul_of_nonneg_left hsq hC
      _ = ε * (C * ε) ^ (2 ^ (n + 1) - 1) := by
            have hp : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
            have h1 : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
            have hk : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by omega
            rw [hk, pow_add, pow_mul, pow_one]
            ring

/-! ## Key Mathematical Insight -/

/-- **Explanation of quadratic convergence**: The Newton error satisfies
    eₙ₊₁ = (f''(ξₙ)/(2f'(xₙ))) · eₙ²
    so if |C · eₙ| < 1 with C = M/(2m), then |eₙ₊₁| < |eₙ|.
    Moreover, the number of correct digits roughly doubles each iteration:
    - If |e₀| ≈ 10⁻¹ then |e₁| ≈ 10⁻², |e₂| ≈ 10⁻⁴, |e₃| ≈ 10⁻⁸, ...

    This is the core result: the one-step bound is PROVED.
    The full iteration analysis (newton_convergence_rate) requires careful
    tracking of how the constant C evolves as xₙ approaches x*, which
    is handled by the local Lipschitz conditions on f''. -/
theorem newton_error_formula
    {f f'' : ℝ → ℝ} {f' : ℝ → ℝ}
    {x_star x₀ ξ : ℝ}
    (hf_root : f x_star = 0)
    (hf'_nz : f' x₀ ≠ 0)
    (htaylor : f x_star = f x₀ + f' x₀ * (x_star - x₀) + f'' ξ * (x_star - x₀) ^ 2 / 2) :
    newtonStep f f' x₀ - x_star = f'' ξ / (2 * f' x₀) * (x_star - x₀) ^ 2 := by
  simp only [newtonStep]
  have hfx₀ : f x₀ = -f' x₀ * (x_star - x₀) - f'' ξ / 2 * (x_star - x₀) ^ 2 := by
    have h := htaylor; rw [hf_root] at h; linarith
  field_simp [hf'_nz]
  linarith [hfx₀]

end NewtonMethod
