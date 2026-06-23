/-
# Brouwer Fixed Point — OQ-02-OQ-02-OQ-01: a priori / a posteriori error estimates for contraction iteration

The parent `BrouwerFixedPointOQ02OQ02` studies the query complexity of finding
approximate fixed points of contractions, proving the *a posteriori-free* error
bound `|xₙ − x*| ≤ Lⁿ·|x₀ − x*|` (which presupposes knowledge of the unknown
distance `|x₀ − x*|`).  This child supplies the two estimates that make the
contraction iteration *practically computable*, both standard consequences of the
Banach fixed-point setup and both absent from the parent:

  * `apriori_estimate`     — `|xₙ − x*| ≤ Lⁿ/(1−L) · |x₁ − x₀|`.  The bound is
    expressed entirely in terms of the *first step* `|x₁ − x₀|`, computable before
    iterating; it answers "how many steps for accuracy ε?" without knowing `x*`.
  * `aposteriori_estimate` — `|xₙ₊₁ − x*| ≤ L/(1−L) · |xₙ₊₁ − xₙ|`.  The bound
    uses only the *latest step* `|xₙ₊₁ − xₙ|`, giving a computable stopping
    criterion: iterate until the increment is below `(1−L)/L · ε`.

Both follow from the geometric decay `|xₙ − x*| ≤ Lⁿ·|x₀ − x*|` (`iterate_dist`,
reproved here self-containedly) together with the one-step distance estimate
`(1−L)·|x₀ − x*| ≤ |x₁ − x₀|` (`initial_dist`).  We also record the Lipschitz
composition law `|g(f x) − g(f y)| ≤ L₂L₁·|x − y|` (`lipschitz_comp`) and its
corollary that a composite of contractions is a contraction (`contraction_comp`),
the structural fact behind iterating several maps.

All results are fully machine-checked (0 axioms, 0 sorries) and self-contained:
the contraction is given abstractly as `∀ x y, |f x − f y| ≤ L·|x − y|` with a
fixed point `f x* = x*` and the iteration `xₙ₊₁ = f xₙ`.

Reference: Banach (1922); see also the query-complexity parent OQ-02-OQ-02.
-/

import Mathlib

namespace BrouwerOQ02OQ02OQ01

/-- **Geometric decay of the iteration error.**  For a contraction `f` with
    constant `L ≥ 0`, fixed point `x*`, and iteration `xₙ₊₁ = f xₙ`,
    `|xₙ − x*| ≤ Lⁿ · |x₀ − x*|`.  Reproved self-containedly (the parent states
    the analogous bound on `[0,1]`). -/
theorem iterate_dist (f : ℝ → ℝ) (L : ℝ) (hL0 : 0 ≤ L)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (x : ℕ → ℝ) (hx : ∀ n, x (n + 1) = f (x n))
    (xstar : ℝ) (hfp : f xstar = xstar) (n : ℕ) :
    |x n - xstar| ≤ L ^ n * |x 0 - xstar| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := hf (x n) xstar
    rw [hfp, ← hx n] at h
    calc |x (n + 1) - xstar| ≤ L * |x n - xstar| := h
      _ ≤ L * (L ^ n * |x 0 - xstar|) := mul_le_mul_of_nonneg_left ih hL0
      _ = L ^ (n + 1) * |x 0 - xstar| := by ring

/-- **One-step distance estimate.**  `(1 − L)·|x₀ − x*| ≤ |x₁ − x₀|`, equivalently
    `|x₀ − x*| ≤ |x₁ − x₀| / (1 − L)`: the unknown distance to the fixed point is
    controlled by the (computable) first increment. -/
theorem initial_dist (f : ℝ → ℝ) (L : ℝ) (hL1 : L < 1)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (x : ℕ → ℝ) (hx : ∀ n, x (n + 1) = f (x n))
    (xstar : ℝ) (hfp : f xstar = xstar) :
    |x 0 - xstar| ≤ |x 1 - x 0| / (1 - L) := by
  have hcontr : (0 : ℝ) < 1 - L := by linarith
  have ht : |x 0 - xstar| ≤ |x 0 - x 1| + |x 1 - xstar| := abs_sub_le _ _ _
  rw [abs_sub_comm (x 0) (x 1)] at ht
  have hL : |x 1 - xstar| ≤ L * |x 0 - xstar| := by
    have h := hf (x 0) xstar
    rw [hfp, ← hx 0] at h
    exact h
  rw [le_div_iff₀ hcontr]
  nlinarith [ht, hL]

/-- **A priori error estimate.**  `|xₙ − x*| ≤ Lⁿ/(1−L) · |x₁ − x₀|`.  Expressed
    purely in terms of the first increment `|x₁ − x₀|`, so the number of
    iterations needed for a target accuracy can be bounded *before* iterating. -/
theorem apriori_estimate (f : ℝ → ℝ) (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L < 1)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (x : ℕ → ℝ) (hx : ∀ n, x (n + 1) = f (x n))
    (xstar : ℝ) (hfp : f xstar = xstar) (n : ℕ) :
    |x n - xstar| ≤ L ^ n / (1 - L) * |x 1 - x 0| := by
  have hcontr : (0 : ℝ) < 1 - L := by linarith
  have h1 := iterate_dist f L hL0 hf x hx xstar hfp n
  have h2 := initial_dist f L hL1 hf x hx xstar hfp
  have hLn : (0 : ℝ) ≤ L ^ n := pow_nonneg hL0 n
  calc |x n - xstar| ≤ L ^ n * |x 0 - xstar| := h1
    _ ≤ L ^ n * (|x 1 - x 0| / (1 - L)) := mul_le_mul_of_nonneg_left h2 hLn
    _ = L ^ n / (1 - L) * |x 1 - x 0| := by ring

/-- **A posteriori error estimate.**  `|xₙ₊₁ − x*| ≤ L/(1−L) · |xₙ₊₁ − xₙ|`.
    Expressed in terms of the latest increment, giving a computable stopping
    criterion: stop once `|xₙ₊₁ − xₙ| ≤ (1−L)/L · ε`. -/
theorem aposteriori_estimate (f : ℝ → ℝ) (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L < 1)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (x : ℕ → ℝ) (hx : ∀ n, x (n + 1) = f (x n))
    (xstar : ℝ) (hfp : f xstar = xstar) (n : ℕ) :
    |x (n + 1) - xstar| ≤ L / (1 - L) * |x (n + 1) - x n| := by
  have hcontr : (0 : ℝ) < 1 - L := by linarith
  have hstep := hf (x n) xstar
  rw [hfp, ← hx n] at hstep
  have ht : |x n - xstar| ≤ |x n - x (n + 1)| + |x (n + 1) - xstar| := abs_sub_le _ _ _
  rw [abs_sub_comm (x n) (x (n + 1))] at ht
  have hLt := mul_le_mul_of_nonneg_left ht hL0
  have key : (1 - L) * |x (n + 1) - xstar| ≤ L * |x (n + 1) - x n| := by
    nlinarith [hstep, hLt]
  rw [div_mul_eq_mul_div, le_div_iff₀ hcontr]
  nlinarith [key]

/-- **Lipschitz composition law.**  If `f` is `L₁`-Lipschitz and `g` is
    `L₂`-Lipschitz (`L₂ ≥ 0`), then `g ∘ f` is `L₂L₁`-Lipschitz. -/
theorem lipschitz_comp (f g : ℝ → ℝ) (L1 L2 : ℝ) (hL2 : 0 ≤ L2)
    (hf : ∀ x y, |f x - f y| ≤ L1 * |x - y|)
    (hg : ∀ x y, |g x - g y| ≤ L2 * |x - y|) (x y : ℝ) :
    |g (f x) - g (f y)| ≤ (L2 * L1) * |x - y| := by
  calc |g (f x) - g (f y)| ≤ L2 * |f x - f y| := hg (f x) (f y)
    _ ≤ L2 * (L1 * |x - y|) := mul_le_mul_of_nonneg_left (hf x y) hL2
    _ = (L2 * L1) * |x - y| := by ring

/-- **A composite of contractions is a contraction.**  If `f` is an `L₁`-contraction
    and `g` an `L₂`-contraction (`0 ≤ L₁, L₂ < 1`), then `g ∘ f` is a contraction
    with constant `L₂L₁ < 1`. -/
theorem contraction_comp (f g : ℝ → ℝ) (L1 L2 : ℝ)
    (hL1_0 : 0 ≤ L1) (hL1_1 : L1 < 1) (hL2_0 : 0 ≤ L2) (hL2_1 : L2 < 1)
    (hf : ∀ x y, |f x - f y| ≤ L1 * |x - y|)
    (hg : ∀ x y, |g x - g y| ≤ L2 * |x - y|) :
    L2 * L1 < 1 ∧ ∀ x y, |g (f x) - g (f y)| ≤ (L2 * L1) * |x - y| :=
  ⟨by nlinarith, fun x y => lipschitz_comp f g L1 L2 hL2_0 hf hg x y⟩

end BrouwerOQ02OQ02OQ01
