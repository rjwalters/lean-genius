/-
Erdős Problem #1040 — open question oq-03, follow-up oq-02:
"What role does the *monic normalization* play in the lemniscate-area infimum
   μ(F) = inf { area {|f| < 1} : f monic, roots ⊆ F } ?
 For the single-point root set F = {c} the monic value is exactly π (oq-01); what
 happens to the infimum if the leading-coefficient normalization is dropped?"

Parent context.
  * #1040 / oq-03 proved the elementary UPPER bounds  area {|f| < 1} ≤ degree·π.
  * #1040 / oq-03 / oq-01 proved that for the *monic* pure power f(z) = (z - c)^n
    the lemniscate is exactly the open unit disc B(c, 1), of area exactly π, for
    every degree n ≥ 1 — hence μ({c}) ≤ π.

This file isolates the role of the monic normalization. Rescaling the pure power
by a positive real `R` (which rescales the leading coefficient),
   f_R(z) = ((z - c) / R)^n = R^{-n} (z - c)^n        (R > 0),
keeps the single root `c` of multiplicity `n` but changes the leading coefficient
to `R^{-n}` (monic exactly when R = 1). Its lemniscate is the disc of radius `R`:
   {z : |f_R(z)| < 1} = {z : |z - c| < R} = B(c, R),
of area exactly `π R²`. Letting `R` range over `(0, ∞)`:

  * **Monic ⇒ π.** Taking R = 1 (the monic pure power `(z - c)^n`) recovers area
    exactly π, independent of n and c — the oq-01 value, re-derived self-containedly.

  * **Without monicity the area is unconstrained.** The map `R ↦ π R²` is onto
    `(0, ∞)`: every positive area is realised by some single-root degree-`n`
    polynomial, and the areas become arbitrarily small. Hence the infimum of
    lemniscate areas over *all* (not necessarily monic) single-root polynomials
    is `0`.

Conclusion: the monic normalization is *essential* to the finite positive value
π in μ({c}); drop it and the infimum collapses to `0`. This explains why Erdős
#1040 fixes the leading coefficient.

Everything is axiom-free and self-contained: lemniscates are taken of bare
functions `ℂ → ℂ`, so no polynomial-structure scaffolding is needed.
-/

import Mathlib

open Complex MeasureTheory Metric

namespace Erdos1040OQ03OQ02

/-- The lemniscate (open sub-level set) of a function `f : ℂ → ℂ`. -/
def lemOf (f : ℂ → ℂ) : Set ℂ := {z : ℂ | ‖f z‖ < 1}

/-- The rescaled pure power `f_R(z) = ((z - c) / R)^n = R^{-n} (z - c)^n`: a degree-`n`
polynomial with the single root `c` (multiplicity `n`) and leading coefficient
`R^{-n}`. It is monic exactly when `R = 1`. -/
noncomputable def scaledPure (R : ℝ) (c : ℂ) (n : ℕ) : ℂ → ℂ :=
  fun z => ((z - c) / (R : ℂ)) ^ n

@[simp] theorem scaledPure_apply (R : ℝ) (c : ℂ) (n : ℕ) (z : ℂ) :
    scaledPure R c n z = ((z - c) / (R : ℂ)) ^ n := rfl

/-- The monic case `R = 1` is the bare pure power `(z - c)^n`. -/
theorem scaledPure_one (c : ℂ) (n : ℕ) (z : ℂ) :
    scaledPure 1 c n z = (z - c) ^ n := by
  simp [scaledPure]

/-- **The rescaled-pure-power lemniscate is a disc of radius `R`.** For `R > 0` and
`n ≥ 1`,  `{z : |f_R(z)| < 1} = B(c, R)`. -/
theorem lemOf_scaledPure_eq_ball (R : ℝ) (hR : 0 < R) (c : ℂ) {n : ℕ} (hn : 0 < n) :
    lemOf (scaledPure R c n) = Metric.ball c R := by
  ext z
  simp only [lemOf, scaledPure, Set.mem_setOf_eq, norm_pow, norm_div,
    Complex.norm_real, Real.norm_eq_abs, Metric.mem_ball, dist_eq_norm]
  rw [abs_of_pos hR,
    pow_lt_one_iff_of_nonneg (div_nonneg (norm_nonneg _) hR.le) hn.ne']
  exact div_lt_one hR

/-- **Exact area `π R²`.** For `R > 0`, `n ≥ 1`, the rescaled-pure-power lemniscate
has Lebesgue (area) measure exactly `π R²`. -/
theorem volume_lemOf_scaledPure (R : ℝ) (hR : 0 < R) (c : ℂ) {n : ℕ} (hn : 0 < n) :
    volume (lemOf (scaledPure R c n)) = ENNReal.ofReal (Real.pi * R ^ 2) := by
  rw [lemOf_scaledPure_eq_ball R hR c hn, Complex.volume_ball]
  have hpi : ((NNReal.pi : ℝ≥0∞)) = ENNReal.ofReal Real.pi := by
    rw [← NNReal.coe_real_pi]; exact (ENNReal.ofReal_coe_nnreal).symm
  rw [hpi, ← ENNReal.ofReal_pow hR.le,
    ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ R ^ 2 by positivity)]
  congr 1
  ring

/-- **Monic ⇒ area `π`.** With `R = 1` (the monic pure power `(z - c)^n`) the area
is exactly `π`, for every degree `n ≥ 1`. (Re-derives the oq-01 value, here as the
single point `R = 1` of the area function `R ↦ π R²`.) -/
theorem volume_lemOf_monic (c : ℂ) {n : ℕ} (hn : 0 < n) :
    volume (lemOf (scaledPure 1 c n)) = ENNReal.ofReal Real.pi := by
  rw [volume_lemOf_scaledPure 1 one_pos c hn]
  congr 1
  ring

/-- The rescaled-pure-power lemniscate always has *positive* area, for every
`R > 0`, `n ≥ 1`. -/
theorem volume_lemOf_scaledPure_pos (R : ℝ) (hR : 0 < R) (c : ℂ) {n : ℕ}
    (hn : 0 < n) : 0 < volume (lemOf (scaledPure R c n)) := by
  rw [volume_lemOf_scaledPure R hR c hn, ENNReal.ofReal_pos]
  positivity

/-- **Every positive area is realised.** For any target area `A > 0` there is a
single-root degree-`n` polynomial whose lemniscate has area exactly `A` — namely
the rescaling at radius `R = √(A / π)`. -/
theorem area_surjective (c : ℂ) {n : ℕ} (hn : 0 < n) {A : ℝ} (hA : 0 < A) :
    ∃ R : ℝ, 0 < R ∧ volume (lemOf (scaledPure R c n)) = ENNReal.ofReal A := by
  have hAπ : 0 < A / Real.pi := div_pos hA Real.pi_pos
  refine ⟨Real.sqrt (A / Real.pi), Real.sqrt_pos.mpr hAπ, ?_⟩
  rw [volume_lemOf_scaledPure _ (Real.sqrt_pos.mpr hAπ) c hn,
    Real.sq_sqrt hAπ.le]
  congr 1
  rw [mul_comm]
  exact div_mul_cancel₀ A Real.pi_ne_zero

/-- **Areas are unbounded below.** Without the monic normalization the lemniscate
area can be made smaller than any `ε > 0`; hence the infimum of areas over all
single-root degree-`n` polynomials (not necessarily monic) is `0`. -/
theorem area_arbitrarily_small (c : ℂ) {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ volume (lemOf (scaledPure R c n)) < ENNReal.ofReal ε := by
  obtain ⟨R, hRpos, hR⟩ := area_surjective c hn (half_pos hε)
  refine ⟨R, hRpos, ?_⟩
  rw [hR]
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith)

/-- **Capstone: the monic normalization is essential.**
For the single-point root set `{c}`:
* the *monic* representative `(z - c)^n` has lemniscate area exactly `π`,
  independent of the degree `n ≥ 1`; yet
* dropping the normalization, single-root degree-`n` lemniscate areas realise
  *every* positive value and become *arbitrarily small*.
Thus the finite positive infimum `μ({c}) = π` is a consequence of monicity:
without it the infimum collapses to `0`. -/
theorem monic_normalization_essential (c : ℂ) {n : ℕ} (hn : 0 < n) :
    volume (lemOf (scaledPure 1 c n)) = ENNReal.ofReal Real.pi ∧
    (∀ A : ℝ, 0 < A → ∃ R : ℝ, 0 < R ∧
        volume (lemOf (scaledPure R c n)) = ENNReal.ofReal A) ∧
    (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
        volume (lemOf (scaledPure R c n)) < ENNReal.ofReal ε) :=
  ⟨volume_lemOf_monic c hn,
   fun _A hA => area_surjective c hn hA,
   fun _ε hε => area_arbitrarily_small c hn hε⟩

end Erdos1040OQ03OQ02
