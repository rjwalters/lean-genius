import Mathlib

/-!
# The metric Urysohn function is Lipschitz for positively separated sets

The companion file `UrysohnsLemmaOQ01` builds, for disjoint nonempty closed sets `s`, `t`
in a metric space, the explicit Urysohn separator
$$ f(x) \;=\; \frac{d(x,s)}{d(x,s) + d(x,t)} $$
and proves it is *continuous*, vanishes on `s`, equals `1` on `t`, and is `[0,1]`-valued.
Continuity is the qualitative statement; it gives no modulus.

This file upgrades continuity to a **quantitative Lipschitz estimate** whenever the two
sets are *positively separated* — i.e. when the denominator
`D(x) = d(x,s) + d(x,t)` is bounded below by some `δ > 0` (equivalently, when `s` and `t`
sit at positive mutual distance). The headline result `lipschitzWith_urysohnFn` shows that
`f` is then `(1/δ)`-Lipschitz, with the sharp pointwise bound
$$ |f(x) - f(y)| \;\le\; \frac{d(x,y)}{\delta}. $$

The engine is purely algebraic. Writing `a(·) = d(·,s)`, `b(·) = d(·,t)` (each
`1`-Lipschitz, `Metric.lipschitz_infDist_pt`), the quotient difference telescopes to
$$ f(x)-f(y) \;=\; \frac{a(x)\,b(y) - a(y)\,b(x)}{D(x)\,D(y)}, \qquad
   |a(x)b(y) - a(y)b(x)| \;\le\; D(x)\,d(x,y), $$
so `|f(x)-f(y)| ≤ d(x,y)/D(y) ≤ d(x,y)/δ`. A separate lemma
(`delta_le_infDist_add`) discharges the hypothesis from genuine set separation
`∀ p ∈ s, ∀ q ∈ t, δ ≤ dist p q`, and a concrete capstone shows the standard separator of
`{0}` and `{1}` on `ℝ` is `1`-Lipschitz.

All results are over a general `MetricSpace X`, fully machine-checked with no `sorry` and no
extra axioms. The Lipschitz modulus of this explicit function is not a named result in
Mathlib.
-/

namespace UrysohnsLemmaOQ01OQ02

open Set Metric

variable {X : Type*} [MetricSpace X]

/-- The explicit Urysohn function `x ↦ d(x,s) / (d(x,s) + d(x,t))`, repeated from the
companion file `UrysohnsLemmaOQ01` so this file is self-contained. -/
noncomputable def urysohnFn (s t : Set X) (x : X) : ℝ :=
  infDist x s / (infDist x s + infDist x t)

/-- The distance-to-a-set function is `1`-Lipschitz, in the explicit absolute-value form
`|d(x,s) - d(y,s)| ≤ dist x y`. This is the only metric input the Lipschitz estimate needs. -/
theorem abs_infDist_sub_le (s : Set X) (x y : X) :
    |infDist x s - infDist y s| ≤ dist x y := by
  have h := (lipschitz_infDist_pt s).dist_le_mul x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
  exact h

/-- **Positive separation gives a denominator lower bound.** If every pair `p ∈ s`, `q ∈ t`
is at distance at least `δ`, then `d(x,s) + d(x,t) ≥ δ` for *every* `x`: the triangle
inequality propagates the separation of the sets to the sum of distances from an arbitrary
point. Requires `s`, `t` nonempty (else `infDist` collapses to `0`). -/
theorem delta_le_infDist_add {s t : Set X} (hsne : s.Nonempty) (htne : t.Nonempty)
    {δ : ℝ} (hsep : ∀ p ∈ s, ∀ q ∈ t, δ ≤ dist p q) (x : X) :
    δ ≤ infDist x s + infDist x t := by
  have key : δ - infDist x s ≤ infDist x t := by
    rw [le_infDist htne]
    intro q hq
    have hqs : δ ≤ infDist q s := by
      rw [le_infDist hsne]
      intro p hp
      rw [dist_comm]
      exact hsep p hp q hq
    have htri : infDist q s ≤ infDist x s + dist q x := infDist_le_infDist_add_dist
    have hcomb : δ ≤ infDist x s + dist q x := le_trans hqs htri
    rw [dist_comm q x] at hcomb
    linarith
  linarith

/-- **Quantitative Lipschitz bound for the metric Urysohn function.** If the denominator
`d(x,s) + d(x,t)` is bounded below by `δ > 0` everywhere, then
`|f(x) - f(y)| ≤ dist x y / δ`. -/
theorem urysohnFn_abs_sub_le {s t : Set X} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ x, δ ≤ infDist x s + infDist x t) (x y : X) :
    |urysohnFn s t x - urysohnFn s t y| ≤ dist x y / δ := by
  have hDx : 0 < infDist x s + infDist x t := lt_of_lt_of_le hδ (hsep x)
  have hDy : 0 < infDist y s + infDist y t := lt_of_lt_of_le hδ (hsep y)
  have hDx' := hDx.ne'
  have hDy' := hDy.ne'
  -- telescoping identity for the quotient difference
  have hid : urysohnFn s t x - urysohnFn s t y
      = (infDist x s * infDist y t - infDist y s * infDist x t)
          / ((infDist x s + infDist x t) * (infDist y s + infDist y t)) := by
    unfold urysohnFn
    field_simp
    ring
  -- numerator estimate `|a(x)b(y) - a(y)b(x)| ≤ D(x) · dist x y`
  have hnum : |infDist x s * infDist y t - infDist y s * infDist x t|
      ≤ (infDist x s + infDist x t) * dist x y := by
    have e : infDist x s * infDist y t - infDist y s * infDist x t
        = infDist x s * (infDist y t - infDist x t)
          + infDist x t * (infDist x s - infDist y s) := by ring
    have ha : |infDist x s - infDist y s| ≤ dist x y := abs_infDist_sub_le s x y
    have hb : |infDist y t - infDist x t| ≤ dist x y := by
      rw [abs_sub_comm]; exact abs_infDist_sub_le t x y
    rw [e]
    calc |infDist x s * (infDist y t - infDist x t)
            + infDist x t * (infDist x s - infDist y s)|
        ≤ |infDist x s * (infDist y t - infDist x t)|
            + |infDist x t * (infDist x s - infDist y s)| := abs_add_le _ _
      _ = infDist x s * |infDist y t - infDist x t|
            + infDist x t * |infDist x s - infDist y s| := by
          rw [abs_mul, abs_mul, abs_of_nonneg infDist_nonneg, abs_of_nonneg infDist_nonneg]
      _ ≤ infDist x s * dist x y + infDist x t * dist x y := by
          have h1 := mul_le_mul_of_nonneg_left hb (infDist_nonneg (x := x) (s := s))
          have h2 := mul_le_mul_of_nonneg_left ha (infDist_nonneg (x := x) (s := t))
          linarith
      _ = (infDist x s + infDist x t) * dist x y := by ring
  -- assemble
  rw [hid, abs_div, abs_of_pos (mul_pos hDx hDy), div_le_div_iff₀ (mul_pos hDx hDy) hδ]
  -- goal: |num| * δ ≤ dist x y * (D(x) * D(y))
  have hDxd : 0 ≤ (infDist x s + infDist x t) * dist x y :=
    mul_nonneg hDx.le dist_nonneg
  nlinarith [mul_le_mul_of_nonneg_right hnum hδ.le,
    mul_le_mul_of_nonneg_left (hsep y) hDxd, (dist_nonneg : (0:ℝ) ≤ dist x y), hDx, hDy]

/-- **The metric Urysohn function is Lipschitz under positive separation.** Packaged as
`LipschitzWith (1/δ)` for the bundled modulus. -/
theorem lipschitzWith_urysohnFn {s t : Set X} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ x, δ ≤ infDist x s + infDist x t) :
    LipschitzWith (1 / δ).toNNReal (urysohnFn s t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, Real.coe_toNNReal (1 / δ) (by positivity)]
  calc |urysohnFn s t x - urysohnFn s t y| ≤ dist x y / δ :=
        urysohnFn_abs_sub_le hδ hsep x y
    _ = 1 / δ * dist x y := by ring

/-- Lipschitz from genuine set separation: disjoint sets at mutual distance `≥ δ > 0` give a
`(1/δ)`-Lipschitz separator (nonempty closed sets not even required to be closed here — only
nonempty, since separation already forces the denominator bound). -/
theorem lipschitzWith_urysohnFn_of_separated {s t : Set X} (hsne : s.Nonempty)
    (htne : t.Nonempty) {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ p ∈ s, ∀ q ∈ t, δ ≤ dist p q) :
    LipschitzWith (1 / δ).toNNReal (urysohnFn s t) :=
  lipschitzWith_urysohnFn hδ (fun x => delta_le_infDist_add hsne htne hsep x)

/-- As a consequence of being Lipschitz, the separator is (uniformly) continuous — recovering
the companion file's qualitative continuity, now with a modulus. -/
theorem uniformContinuous_urysohnFn {s t : Set X} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ x, δ ≤ infDist x s + infDist x t) :
    UniformContinuous (urysohnFn s t) :=
  (lipschitzWith_urysohnFn hδ hsep).uniformContinuous

/-! ## A concrete capstone on `ℝ` -/

/-- The standard separator of `{0}` and `{1}` on the real line,
`x ↦ |x| / (|x| + |x-1|)`, is `1`-Lipschitz: the two points are at distance `1`, so
`δ = 1` and the modulus is `1/δ = 1`. -/
theorem lipschitzWith_urysohnFn_zero_one :
    LipschitzWith 1 (urysohnFn ({0} : Set ℝ) {1}) := by
  have hsep : ∀ x : ℝ, (1 : ℝ) ≤ infDist x {0} + infDist x {1} := by
    intro x
    rw [infDist_singleton, infDist_singleton, Real.dist_eq, Real.dist_eq]
    have h := abs_add_le x (1 - x)
    have hsum : x + (1 - x) = 1 := by ring
    rw [hsum, abs_one] at h
    have hflip : |1 - x| = |x - 1| := abs_sub_comm 1 x
    rw [hflip] at h
    simpa [sub_zero] using h
  have := lipschitzWith_urysohnFn (s := ({0} : Set ℝ)) (t := {1}) (δ := 1) one_pos hsep
  simpa using this

end UrysohnsLemmaOQ01OQ02
