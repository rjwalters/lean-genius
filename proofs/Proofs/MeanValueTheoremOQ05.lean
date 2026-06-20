import Mathlib

/-!
# Darboux's Theorem — the Intermediate Value Property of Derivatives

This file formalizes **Darboux's theorem**: a derivative satisfies the
intermediate value property *even when it is not continuous*. If `f` is
differentiable on `[a, b]`, then `f'` takes every value between `f'(a)` and
`f'(b)` on `[a, b]`. Equivalently, the image of an order-connected set under a
derivative is again order-connected — derivatives have **no jump
discontinuities**.

This is a genuinely different phenomenon from the ordinary Mean Value Theorem
(Rolle / Lagrange / Cauchy) and from the FTC: it constrains the *range* of `f'`
without assuming `f'` is continuous. A classic consequence is that a function
like `sgn` can never be a derivative.

## Key Results

1. `darboux_ivp` — closed form: if `m ∈ [[f'(a), f'(b)]]` then `f' c = m` for
   some `c ∈ [a, b]` (no continuity of `f'` required).
2. `darboux_ivp_open` — strict form: if `m` is strictly between `f'(a)` and
   `f'(b)` then `f' c = m` for some `c` in the **open** interval `(a, b)`.
3. `darboux_ivp_deriv` — the same stated directly for `deriv f`.
4. `deriv_range_ordConnected` — the range of `deriv f` over an order-connected
   set is order-connected (no jumps).
5. `deriv_range_convex` — the convex repackaging of the same fact.
6. `not_deriv_of_jump` — a function whose putative "derivative" skips a value
   strictly between two attained values cannot be a derivative.
7. `darboux_sq_example` — a concrete witness: `deriv (·²)` hits `1` on `[0, 2]`.

## Context

This answers OQ-05 for the MVT gallery. The existing entries cover Rolle /
Lagrange / Cauchy (base), monotonicity from the derivative (oq-03), Taylor
(oq-02), and the FTC (oq-04). None of them state the intermediate value
property *of the derivative itself*, which is the orthogonal "shape of `f'`"
result. The Mathlib vehicle is `Mathlib.Analysis.Calculus.Darboux`.
-/

namespace MeanValueTheoremOQ05

open Set

variable {f f' : ℝ → ℝ} {a b : ℝ}

/-- **Darboux's theorem (closed form).** If `f` is differentiable on `[a, b]`
with derivative `f'`, then `f'` attains every value in the closed interval
`[[f'(a), f'(b)]]` somewhere on `[a, b]` — *without* assuming `f'` is
continuous. -/
theorem darboux_ivp (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    {m : ℝ} (hm : m ∈ uIcc (f' a) (f' b)) :
    ∃ c ∈ Icc a b, f' c = m := by
  have hoc : OrdConnected (f' '' Icc a b) := ordConnected_Icc.image_hasDerivWithinAt hf
  have ha : f' a ∈ f' '' Icc a b := mem_image_of_mem _ (left_mem_Icc.2 hab)
  have hb : f' b ∈ f' '' Icc a b := mem_image_of_mem _ (right_mem_Icc.2 hab)
  exact hoc.uIcc_subset ha hb hm

/-- **Darboux's theorem (strict / open form).** If `m` lies strictly between
`f'(a)` and `f'(b)`, the value is attained in the *open* interval `(a, b)`. -/
theorem darboux_ivp_open (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    {m : ℝ} (hm : m ∈ Ioo (min (f' a) (f' b)) (max (f' a) (f' b))) :
    ∃ c ∈ Ioo a b, f' c = m := by
  rcases le_total (f' a) (f' b) with h | h
  · rw [min_eq_left h, max_eq_right h] at hm
    exact exists_hasDerivWithinAt_eq_of_gt_of_lt hab hf hm.1 hm.2
  · rw [min_eq_right h, max_eq_left h] at hm
    exact exists_hasDerivWithinAt_eq_of_lt_of_gt hab hf hm.2 hm.1

/-- Darboux's theorem stated directly for `deriv f`, assuming `f` is
differentiable at each point of `[a, b]`. -/
theorem darboux_ivp_deriv (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    {m : ℝ} (hm : m ∈ uIcc (deriv f a) (deriv f b)) :
    ∃ c ∈ Icc a b, deriv f c = m :=
  darboux_ivp hab (fun x hx => (hf x hx).hasDerivAt.hasDerivWithinAt) hm

/-- **No jump discontinuities.** The image of an order-connected set under
`deriv f` is order-connected. This is the structural form of Darboux's
theorem: a derivative cannot skip values. -/
theorem deriv_range_ordConnected {s : Set ℝ} (hs : OrdConnected s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) :
    OrdConnected (deriv f '' s) :=
  hs.image_deriv hf

/-- Convex repackaging: the image of a convex set under `deriv f` is convex. -/
theorem deriv_range_convex {s : Set ℝ} (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) :
    Convex ℝ (deriv f '' s) :=
  hs.image_deriv hf

/-- **Consequence: a function with a gap is not a derivative.** Suppose `g`
takes the values `g(a)` and `g(b)` (with `a ≤ b`) but never takes some value
`m` strictly between them on `[a, b]`. Then `g` is not the derivative of any
function on `[a, b]`. (Stated contrapositively to Darboux.) -/
theorem not_deriv_of_jump (hab : a ≤ b) {g : ℝ → ℝ} {m : ℝ}
    (hm : m ∈ uIcc (g a) (g b)) (hgap : ∀ x ∈ Icc a b, g x ≠ m) :
    ¬ ∀ x ∈ Icc a b, HasDerivWithinAt f (g x) (Icc a b) x := by
  intro hf
  obtain ⟨c, hc, hcm⟩ := darboux_ivp hab hf hm
  exact hgap c hc hcm

/-- A concrete witness for Darboux's theorem: the derivative of `x ↦ x²` runs
from `0` to `4` on `[0, 2]`, so it must hit the intermediate value `1` — and
indeed `deriv (·²) (1/2) = 1`. -/
theorem darboux_sq_example :
    ∃ c ∈ Icc (0 : ℝ) 2, (fun x => 2 * x) c = 1 := by
  have hf : ∀ x ∈ Icc (0 : ℝ) 2,
      HasDerivWithinAt (fun x => x ^ 2) ((fun x => 2 * x) x) (Icc 0 2) x := by
    intro x _
    have h : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    exact h.hasDerivWithinAt
  refine darboux_ivp (by norm_num) hf ?_
  rw [uIcc_of_le (by norm_num)]
  constructor <;> norm_num

end MeanValueTheoremOQ05
