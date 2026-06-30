/-
# Gautschi-Type Ratio Bounds for the Gamma Function

The Gamma function `Γ` is **logarithmically convex** on `(0, ∞)` — a fact recorded
in Mathlib as `Real.convexOn_log_Gamma`. From this single structural input, together
with the functional equation `Γ(x+1) = x · Γ(x)`, we derive the classical
**Gautschi double inequality** for the ratio of Gamma values at unit-shifted points:

  for `x > 0` and `0 < s < 1`,    `x^(1-s) ≤ Γ(x+1) / Γ(x+s) ≤ (x+1)^(1-s)`.

These ratio bounds are *not* in Mathlib (which records the convexity but none of the
Gautschi/Kershaw ratio estimates). Both directions follow purely from log-convexity,
applied to two different convex decompositions:

* lower bound: `x+s = (1-s)·x + s·(x+1)`  (convexity gives `Γ(x+s) ≤ Γ(x)·x^s`);
* upper bound: `x+1 = (1/(2-s))·(x+s) + ((1-s)/(2-s))·(x+2)`.

We also package the multiplicative midpoint inequality `Γ((a+b)/2)^2 ≤ Γ(a)·Γ(b)`,
the cleanest direct consequence of midpoint log-convexity.

All results are fully verified (0 sorries, 0 axioms beyond Lean's foundations).
-/
import Mathlib

open Real Set

namespace GammaLogConvexityOQ01

/-- Functional-equation form of `log ∘ Γ`: `log Γ(x+1) = log x + log Γ(x)` for `x > 0`. -/
lemma logGamma_add_one {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma (x + 1)) = Real.log x + Real.log (Real.Gamma x) := by
  rw [Real.Gamma_add_one hx.ne', Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne']

/-- Core convexity estimate (lower side): for `x > 0`, `0 ≤ s ≤ 1`,
`log Γ(x+s) ≤ log Γ(x) + s · log x`. Obtained from log-convexity using the convex
combination `x + s = (1-s)·x + s·(x+1)`. -/
lemma logGamma_le_lower {x s : ℝ} (hx : 0 < x) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.log (Real.Gamma (x + s)) ≤ Real.log (Real.Gamma x) + s * Real.log x := by
  have h := convexOn_log_Gamma.2 (Set.mem_Ioi.mpr hx)
    (Set.mem_Ioi.mpr (by linarith : (0 : ℝ) < x + 1))
    (by linarith : (0 : ℝ) ≤ 1 - s) hs0 (by ring)
  simp only [Function.comp_apply, smul_eq_mul] at h
  rw [show (1 - s) * x + s * (x + 1) = x + s by ring, logGamma_add_one hx] at h
  have e : (1 - s) * Real.log (Real.Gamma x)
      + s * (Real.log x + Real.log (Real.Gamma x))
      = Real.log (Real.Gamma x) + s * Real.log x := by ring
  rw [e] at h
  exact h

/-- **Gautschi lower bound.** For `x > 0` and `0 < s < 1`,
`x^(1-s) ≤ Γ(x+1) / Γ(x+s)`. -/
theorem gautschi_lower {x s : ℝ} (hx : 0 < x) (hs0 : 0 < s) (hs1 : s < 1) :
    x ^ (1 - s) ≤ Real.Gamma (x + 1) / Real.Gamma (x + s) := by
  have hxs : 0 < x + s := by linarith
  have hGxs : 0 < Real.Gamma (x + s) := Real.Gamma_pos_of_pos hxs
  have hGx : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  -- log Γ(x+s) ≤ log Γ x + s · log x
  have hlog := logGamma_le_lower hx hs0.le hs1.le
  -- exponentiate to Γ(x+s) ≤ Γ x · x^s
  have hGxs_le : Real.Gamma (x + s) ≤ Real.Gamma x * x ^ s := by
    have hb : 0 < Real.Gamma x * x ^ s := by positivity
    have hlog2 : Real.log (Real.Gamma (x + s)) ≤ Real.log (Real.Gamma x * x ^ s) := by
      rw [Real.log_mul hGx.ne' (by positivity), Real.log_rpow hx]
      exact hlog
    have := Real.exp_le_exp.mpr hlog2
    rwa [Real.exp_log hGxs, Real.exp_log hb] at this
  -- assemble the ratio bound
  rw [le_div_iff₀ hGxs, Real.Gamma_add_one hx.ne']
  have hxpow : x ^ (1 - s) * x ^ s = x := by
    rw [← Real.rpow_add hx, show (1 : ℝ) - s + s = 1 by ring, Real.rpow_one]
  calc
    x ^ (1 - s) * Real.Gamma (x + s)
        ≤ x ^ (1 - s) * (Real.Gamma x * x ^ s) :=
          mul_le_mul_of_nonneg_left hGxs_le (by positivity)
    _ = (x ^ (1 - s) * x ^ s) * Real.Gamma x := by ring
    _ = x * Real.Gamma x := by rw [hxpow]

/-- **Gautschi upper bound.** For `x > 0` and `0 < s < 1`,
`Γ(x+1) / Γ(x+s) ≤ (x+1)^(1-s)`. -/
theorem gautschi_upper {x s : ℝ} (hx : 0 < x) (hs0 : 0 < s) (hs1 : s < 1) :
    Real.Gamma (x + 1) / Real.Gamma (x + s) ≤ (x + 1) ^ (1 - s) := by
  have hxs : 0 < x + s := by linarith
  have hx1 : 0 < x + 1 := by linarith
  have hx2 : 0 < x + 2 := by linarith
  have h2s : 0 < 2 - s := by linarith
  have hGxs : 0 < Real.Gamma (x + s) := Real.Gamma_pos_of_pos hxs
  have hGx1 : 0 < Real.Gamma (x + 1) := Real.Gamma_pos_of_pos hx1
  -- convexity via x+1 = (1/(2-s))·(x+s) + ((1-s)/(2-s))·(x+2)
  have h := convexOn_log_Gamma.2 (Set.mem_Ioi.mpr hxs) (Set.mem_Ioi.mpr hx2)
    (div_nonneg (by norm_num) (by linarith) : (0 : ℝ) ≤ 1 / (2 - s))
    (div_nonneg (by linarith) (by linarith) : (0 : ℝ) ≤ (1 - s) / (2 - s))
    (by field_simp; ring)
  simp only [Function.comp_apply, smul_eq_mul] at h
  rw [show 1 / (2 - s) * (x + s) + (1 - s) / (2 - s) * (x + 2) = x + 1 by
    field_simp; ring] at h
  -- log Γ(x+2) = log(x+1) + log Γ(x+1)
  have hG2 : Real.log (Real.Gamma (x + 2))
      = Real.log (x + 1) + Real.log (Real.Gamma (x + 1)) := by
    rw [show (x : ℝ) + 2 = (x + 1) + 1 by ring, logGamma_add_one hx1]
  rw [hG2] at h
  -- clear the denominator (2-s) and simplify
  have h' := mul_le_mul_of_nonneg_left h h2s.le
  have hsimp : (2 - s) * (1 / (2 - s) * Real.log (Real.Gamma (x + s))
      + (1 - s) / (2 - s) * (Real.log (x + 1) + Real.log (Real.Gamma (x + 1))))
      = Real.log (Real.Gamma (x + s))
        + (1 - s) * (Real.log (x + 1) + Real.log (Real.Gamma (x + 1))) := by
    field_simp
  rw [hsimp] at h'
  -- linear rearrangement: log Γ(x+1) − log Γ(x+s) ≤ (1-s) log(x+1)
  have hmul : Real.log (Real.Gamma (x + 1)) - Real.log (Real.Gamma (x + s))
      ≤ (1 - s) * Real.log (x + 1) := by nlinarith [h']
  -- exponentiate
  have hlogdiv : Real.log (Real.Gamma (x + 1) / Real.Gamma (x + s))
      ≤ Real.log ((x + 1) ^ (1 - s)) := by
    rw [Real.log_div hGx1.ne' hGxs.ne', Real.log_rpow hx1]
    exact hmul
  have hpos : 0 < Real.Gamma (x + 1) / Real.Gamma (x + s) := div_pos hGx1 hGxs
  have := Real.exp_le_exp.mpr hlogdiv
  rwa [Real.exp_log hpos, Real.exp_log (by positivity : (0 : ℝ) < (x + 1) ^ (1 - s))] at this

/-- **Gautschi double inequality** (combined two-sided form). For `x > 0` and
`0 < s < 1`, the unit-shift ratio of Gamma values is bracketed by powers:
`x^(1-s) ≤ Γ(x+1)/Γ(x+s) ≤ (x+1)^(1-s)`. -/
theorem gautschi_bracket {x s : ℝ} (hx : 0 < x) (hs0 : 0 < s) (hs1 : s < 1) :
    x ^ (1 - s) ≤ Real.Gamma (x + 1) / Real.Gamma (x + s)
      ∧ Real.Gamma (x + 1) / Real.Gamma (x + s) ≤ (x + 1) ^ (1 - s) :=
  ⟨gautschi_lower hx hs0 hs1, gautschi_upper hx hs0 hs1⟩

/-- **Multiplicative midpoint inequality.** For `a, b > 0`,
`Γ((a+b)/2)^2 ≤ Γ(a) · Γ(b)`, the direct multiplicative form of midpoint
log-convexity of `Γ`. -/
theorem gamma_midpoint_sq_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.Gamma ((a + b) / 2) ^ 2 ≤ Real.Gamma a * Real.Gamma b := by
  have hmid : 0 < (a + b) / 2 := by linarith
  have hGa : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hGb : 0 < Real.Gamma b := Real.Gamma_pos_of_pos hb
  have h := convexOn_log_Gamma.2 (Set.mem_Ioi.mpr ha) (Set.mem_Ioi.mpr hb)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [Function.comp_apply, smul_eq_mul] at h
  rw [show 1 / 2 * a + 1 / 2 * b = (a + b) / 2 by ring] at h
  have hlog : Real.log (Real.Gamma ((a + b) / 2) ^ 2)
      ≤ Real.log (Real.Gamma a * Real.Gamma b) := by
    rw [Real.log_pow, Real.log_mul hGa.ne' hGb.ne']
    push_cast
    linarith [h]
  have := Real.exp_le_exp.mpr hlog
  rwa [Real.exp_log (by positivity), Real.exp_log (by positivity)] at this

end GammaLogConvexityOQ01
