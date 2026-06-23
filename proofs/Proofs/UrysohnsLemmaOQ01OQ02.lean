import Mathlib

/-
# The metric Urysohn function is Lipschitz for positively separated sets

**Open question (`urysohns-lemma-oq-01-oq-02`).** The parent entry
`Proofs/UrysohnsLemmaOQ01.lean` constructs the explicit metric Urysohn function
separating two disjoint nonempty closed sets `s`, `t` in a metric space,
$$ f(x) \;=\; \frac{d(x,s)}{d(x,s) + d(x,t)}, $$
and proves it is continuous, valued in `[0,1]`, and equal to `0` on `s` and `1`
on `t`. Continuity is purely qualitative. This file supplies the **quantitative**
regularity the parent leaves open:

> when the two sets are a fixed positive distance apart — `δ ≤ d(a,b)` for every
> `a ∈ s`, `b ∈ t` — the function `f` is **Lipschitz**, with modulus `δ⁻¹`
> determined by the separation gap.

The argument is elementary and needs neither closedness nor disjointness as
separate hypotheses (positive separation subsumes both):

* **Separation lower bound** (`sep_le_infDist_add`). For every `x`,
  `δ ≤ d(x,s) + d(x,t)`. Indeed for `a ∈ s`, `b ∈ t`,
  `δ ≤ d(a,b) ≤ d(x,a) + d(x,b)`; taking the infimum over `a` then over `b`
  (via `Metric.le_infDist`) gives the claim. In particular the denominator is
  `≥ δ > 0` everywhere.

* **One-Lipschitz distance functions** (`abs_infDist_sub_le`).
  `|d(x,s) - d(y,s)| ≤ d(x,y)`, from `Metric.infDist_le_infDist_add_dist`.

* **The quotient estimate.** Writing `u = d(·,s)`, `v = d(·,t)`, `g = u+v`,
  `f(x) - f(y) = (u(x)v(y) - u(y)v(x)) / (g(x)g(y))`, and the numerator is bounded
  by `g(x)·d(x,y)` because `|u(x)v(y) - u(y)v(x)| = |u(x)(v(y)-v(x)) +
  v(x)(u(x)-u(y))| ≤ (u(x)+v(x))·d(x,y)`. Dividing,
  `|f(x) - f(y)| ≤ d(x,y) / g(y) ≤ δ⁻¹·d(x,y)`.

Headline results: the sharp pointwise estimate `δ·|f(x)-f(y)| ≤ d(x,y)`
(`mul_dist_urysohnFn_le`), the Lipschitz constant `δ⁻¹` (`dist_urysohnFn_le`),
the bundled `LipschitzWith` statement (`lipschitzWith_urysohnFn`), and uniform
continuity (`uniformContinuous_urysohnFn`). A concrete instance on `ℝ`
({0} and {1}, gap `1`) yields a `1`-Lipschitz function.

All results are fully machine-checked with no `sorry` and no extra axioms.
-/

namespace UrysohnsLemmaOQ01OQ02

open Set Metric

variable {X : Type*} [MetricSpace X]

/-- The explicit Urysohn function separating two sets in a metric space:
`x ↦ d(x, s) / (d(x, s) + d(x, t))`. (Same construction as the parent entry,
restated here so this file is self-contained.) -/
noncomputable def urysohnFn (s t : Set X) (x : X) : ℝ :=
  infDist x s / (infDist x s + infDist x t)

/-! ## Two preparatory lemmas -/

/-- **Separation lower bound.** If `s`, `t` are nonempty and separated by a gap
`δ` (`δ ≤ d(a,b)` for all `a ∈ s`, `b ∈ t`), then `δ ≤ d(x,s) + d(x,t)` for every
point `x`. In particular the denominator of the Urysohn function is `≥ δ`. -/
theorem sep_le_infDist_add {s t : Set X} {δ : ℝ}
    (hsne : s.Nonempty) (htne : t.Nonempty)
    (hsep : ∀ a ∈ s, ∀ b ∈ t, δ ≤ dist a b) (x : X) :
    δ ≤ infDist x s + infDist x t := by
  -- For every `b ∈ t`, `δ - d(x,b) ≤ d(x,s)`, by infimum over `a ∈ s`.
  have hA : ∀ b ∈ t, δ - dist x b ≤ infDist x s := by
    intro b hb
    rw [Metric.le_infDist hsne]
    intro a ha
    have hsab := hsep a ha b hb
    have htri : dist a b ≤ dist x a + dist x b := by
      rw [dist_comm x a]; exact dist_triangle a x b
    linarith
  -- Hence `δ - d(x,s) ≤ d(x,t)`, by infimum over `b ∈ t`.
  have hB : δ - infDist x s ≤ infDist x t := by
    rw [Metric.le_infDist htne]
    intro b hb
    have := hA b hb
    linarith
  linarith

/-- The distance-to-a-set function `x ↦ d(x,s)` is `1`-Lipschitz:
`|d(x,s) - d(y,s)| ≤ d(x,y)`. -/
theorem abs_infDist_sub_le (s : Set X) (x y : X) :
    |infDist x s - infDist y s| ≤ dist x y := by
  rw [abs_sub_le_iff]
  refine ⟨?_, ?_⟩
  · have h := Metric.infDist_le_infDist_add_dist (x := x) (y := y) (s := s)
    linarith
  · have h := Metric.infDist_le_infDist_add_dist (x := y) (y := x) (s := s)
    rw [dist_comm] at h; linarith

/-! ## The Lipschitz estimate -/

/-- **Sharp pointwise estimate.** For positively separated nonempty sets,
`δ · |f(x) - f(y)| ≤ d(x,y)`, i.e. the explicit Urysohn function `f = urysohnFn s t`
contracts distances by the gap `δ`. -/
theorem mul_dist_urysohnFn_le {s t : Set X} {δ : ℝ} (hδ : 0 < δ)
    (hsne : s.Nonempty) (htne : t.Nonempty)
    (hsep : ∀ a ∈ s, ∀ b ∈ t, δ ≤ dist a b) (x y : X) :
    δ * |urysohnFn s t x - urysohnFn s t y| ≤ dist x y := by
  have hgx : δ ≤ infDist x s + infDist x t := sep_le_infDist_add hsne htne hsep x
  have hgy : δ ≤ infDist y s + infDist y t := sep_le_infDist_add hsne htne hsep y
  have hgx0 : 0 < infDist x s + infDist x t := hδ.trans_le hgx
  have hgy0 : 0 < infDist y s + infDist y t := hδ.trans_le hgy
  have hu0 : 0 ≤ infDist x s := infDist_nonneg
  have hv0 : 0 ≤ infDist x t := infDist_nonneg
  have hD : 0 ≤ dist x y := dist_nonneg
  have hu : |infDist x s - infDist y s| ≤ dist x y := abs_infDist_sub_le s x y
  have hv : |infDist x t - infDist y t| ≤ dist x y := abs_infDist_sub_le t x y
  unfold urysohnFn
  set u := infDist x s with hu_def
  set v := infDist x t with hv_def
  set u' := infDist y s with hu'_def
  set v' := infDist y t with hv'_def
  set D := dist x y with hD_def
  -- Numerator bound: `|u(u'+v') - (u+v)u'| ≤ (u+v)·D`.
  have hN : |u * (u' + v') - (u + v) * u'| ≤ (u + v) * D := by
    have e : u * (u' + v') - (u + v) * u' = u * (v' - v) + v * (u - u') := by ring
    rw [e]
    calc |u * (v' - v) + v * (u - u')|
        ≤ |u * (v' - v)| + |v * (u - u')| := abs_add_le _ _
      _ = u * |v' - v| + v * |u - u'| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hu0, abs_of_nonneg hv0]
      _ ≤ u * D + v * D := by
          refine add_le_add (mul_le_mul_of_nonneg_left ?_ hu0)
            (mul_le_mul_of_nonneg_left hu hv0)
          rw [abs_sub_comm]; exact hv
      _ = (u + v) * D := by ring
  rw [div_sub_div _ _ hgx0.ne' hgy0.ne', abs_div,
    abs_of_pos (mul_pos hgx0 hgy0), ← mul_div_assoc,
    div_le_iff₀ (mul_pos hgx0 hgy0)]
  have h_a : δ * |u * (u' + v') - (u + v) * u'| ≤ δ * ((u + v) * D) :=
    mul_le_mul_of_nonneg_left hN hδ.le
  have h_b : δ * ((u + v) * D) ≤ (u' + v') * ((u + v) * D) :=
    mul_le_mul_of_nonneg_right hgy (mul_nonneg hgx0.le hD)
  nlinarith [h_a, h_b]

/-- **Lipschitz modulus.** For positively separated nonempty sets, the explicit
Urysohn function satisfies `|f(x) - f(y)| ≤ δ⁻¹·d(x,y)`. -/
theorem dist_urysohnFn_le {s t : Set X} {δ : ℝ} (hδ : 0 < δ)
    (hsne : s.Nonempty) (htne : t.Nonempty)
    (hsep : ∀ a ∈ s, ∀ b ∈ t, δ ≤ dist a b) (x y : X) :
    |urysohnFn s t x - urysohnFn s t y| ≤ δ⁻¹ * dist x y := by
  have hmul := mul_dist_urysohnFn_le hδ hsne htne hsep x y
  have hδinv : (0 : ℝ) ≤ δ⁻¹ := by positivity
  have h := mul_le_mul_of_nonneg_left hmul hδinv
  rwa [← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul] at h

/-- **`LipschitzWith` packaging.** The explicit Urysohn function for sets
separated by gap `δ > 0` is `δ⁻¹`-Lipschitz. -/
theorem lipschitzWith_urysohnFn {s t : Set X} {δ : ℝ} (hδ : 0 < δ)
    (hsne : s.Nonempty) (htne : t.Nonempty)
    (hsep : ∀ a ∈ s, ∀ b ∈ t, δ ≤ dist a b) :
    LipschitzWith (Real.toNNReal δ⁻¹) (urysohnFn s t) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [Real.dist_eq, Real.coe_toNNReal δ⁻¹ (by positivity)]
  exact dist_urysohnFn_le hδ hsne htne hsep x y

/-- The explicit Urysohn function for positively separated sets is uniformly
continuous (immediate from the Lipschitz bound). -/
theorem uniformContinuous_urysohnFn {s t : Set X} {δ : ℝ} (hδ : 0 < δ)
    (hsne : s.Nonempty) (htne : t.Nonempty)
    (hsep : ∀ a ∈ s, ∀ b ∈ t, δ ≤ dist a b) :
    UniformContinuous (urysohnFn s t) :=
  (lipschitzWith_urysohnFn hδ hsne htne hsep).uniformContinuous

/-- **Explicit modulus of continuity in terms of the gap.** If `d(x,y) < δ·ε`
then the Urysohn values are within `ε`. This makes the dependence of the modulus
on the separation gap quantitative. -/
theorem dist_urysohnFn_lt {s t : Set X} {δ ε : ℝ} (hδ : 0 < δ)
    (hsne : s.Nonempty) (htne : t.Nonempty)
    (hsep : ∀ a ∈ s, ∀ b ∈ t, δ ≤ dist a b) {x y : X}
    (hxy : dist x y < δ * ε) :
    |urysohnFn s t x - urysohnFn s t y| < ε := by
  have h := dist_urysohnFn_le hδ hsne htne hsep x y
  have hδinv : (0 : ℝ) < δ⁻¹ := inv_pos.mpr hδ
  calc |urysohnFn s t x - urysohnFn s t y| ≤ δ⁻¹ * dist x y := h
    _ < δ⁻¹ * (δ * ε) := mul_lt_mul_of_pos_left hxy hδinv
    _ = ε := by rw [← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul]

/-! ## A concrete instance on `ℝ` -/

/-- On `ℝ`, the singletons `{0}` and `{1}` are separated by gap `1`, so the
explicit Urysohn function separating them is `1`-Lipschitz. -/
example : LipschitzWith 1 (urysohnFn ({0} : Set ℝ) {1}) := by
  have hcoe : Real.toNNReal (1 : ℝ)⁻¹ = 1 := by
    rw [inv_one, Real.toNNReal_one]
  rw [← hcoe]
  refine lipschitzWith_urysohnFn (by norm_num) ⟨0, rfl⟩ ⟨1, rfl⟩ ?_
  intro a ha b hb
  rw [Set.mem_singleton_iff] at ha hb
  subst ha; subst hb
  rw [Real.dist_eq]; norm_num

end UrysohnsLemmaOQ01OQ02
