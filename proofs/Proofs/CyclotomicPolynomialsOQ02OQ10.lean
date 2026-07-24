/-
Erdős Problem #1215 — cyclotomic restriction (OQ-02): the sublevel labyrinth is
DISCONNECTED for small `C` — and, for `n = 4`, at the question's own level `C = 1`.

Prior OQ-02 layers pinned the metric geometry of `{z : |Φ_n(z)| < C}` (radius and area
sandwiches, both sides sharp), a radial exit path along `ℝ_{≥0}` (OQ02OQ08), and the fact
that the *superlevel* far field is one connected escape region (OQ02OQ09). None of them
touched the connectivity of the sublevel set itself — the genuinely open Mac Lane driver
is its component count.

This file lands the first component-count fact, in the negative direction: **for every
`n ≥ 3` the sublevel set is disconnected once `C` is small enough**, with the explicit
threshold `C ≤ imProd n := ∏_{ζ primitive} |Im ζ|`. Mechanism:

* on the real axis, `|Φ_n(x)| = ∏_ζ |x - ζ| ≥ ∏_ζ |Im ζ| = imProd n` — a real point is
  at least `|Im ζ|` away from each (non-real) root;
* for `n ≥ 3` no primitive `n`-th root of unity is real, so `imProd n > 0`;
* hence for `C ≤ imProd n` the sublevel set avoids the real axis entirely, while still
  containing the conjugate pair of roots `ζ = e^{2πi/n}` (upper half-plane) and
  `ζ⁻¹ = e^{-2πi/n}` (lower half-plane): the two open half-planes disconnect it.

Sharpness of the threshold in the family's key instance: `Φ₄ = X² + 1` has
`imProd 4 = |Im i| · |Im (-i)| = 1`, so the disconnection holds at `C = 1` — the exact
level of Erdős #1215's sublevel set `{|Φ_n| < 1}`. The `n = 4` "labyrinth" at the
question's own threshold is two disjoint Cassini lobes around `±i`, and any path-length
analysis decomposes lobe-by-lobe. (Contrast `n = 3`: `|Φ₃(-1/2)| = 3/4 < 1`, so the
`C = 1` sublevel set *does* meet the real axis — the disconnection threshold is genuinely
`n`-dependent.)

## Main results
* `norm_real_sub_ge_abs_im`     : `|Im ζ| ≤ ‖(x : ℂ) - ζ‖` for real `x`.
* `imProd`                      : `∏_{ζ ∈ primitiveRoots n ℂ} |Im ζ|`.
* `imProd_le_norm_cyclotomic_eval_real` : `imProd n ≤ ‖Φ_n(x)‖` for all real `x`.
* `not_isReal_of_isPrimitiveRoot`  : for `n ≥ 3`, primitive `n`-th roots of unity have
                                     nonzero imaginary part.
* `imProd_pos`                  : `0 < imProd n` for `n ≥ 3`.
* `sublevel_avoids_real`        : `C ≤ imProd n` ⟹ the sublevel set misses `{Im = 0}`.
* `cyclotomic_sublevel_not_isPreconnected` : for `n ≥ 3`, `0 < C ≤ imProd n`, the set
                                     `{z : ‖Φ_n(z)‖ < C}` is NOT preconnected.

Everything is unconditional (0 axioms, 0 sorries; imports Mathlib only).
-/
import Mathlib

open Polynomial

namespace CyclotomicPolynomialsOQ02OQ10

/-! ## The real-axis lower bound -/

/-- A real point is at least `|Im ζ|` away from any complex number `ζ`. -/
theorem norm_real_sub_ge_abs_im (x : ℝ) (ζ : ℂ) : |ζ.im| ≤ ‖(x : ℂ) - ζ‖ := by
  have h1 : ((x : ℂ) - ζ).im = -ζ.im := by simp
  calc |ζ.im| = |((x : ℂ) - ζ).im| := by rw [h1, abs_neg]
    _ ≤ ‖(x : ℂ) - ζ‖ := Complex.abs_im_le_norm _

/-- The product of `|Im ζ|` over the primitive `n`-th roots of unity in `ℂ`. -/
noncomputable def imProd (n : ℕ) : ℝ := ∏ ζ ∈ primitiveRoots n ℂ, |ζ.im|

/-- **Real-axis lower bound**: for every real `x`,
`imProd n ≤ ‖Φ_n(x)‖`. Each root factor `|x - ζ|` is at least `|Im ζ|`. -/
theorem imProd_le_norm_cyclotomic_eval_real (n : ℕ) (hn : n ≠ 0) (x : ℝ) :
    imProd n ≤ ‖(cyclotomic n ℂ).eval (x : ℂ)‖ := by
  obtain ⟨ζ₀, hζ₀⟩ := Complex.isPrimitiveRoot_exp n hn
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots hζ₀, eval_prod]
  rw [norm_prod]
  refine Finset.prod_le_prod (fun ζ _ => abs_nonneg _) (fun ζ _ => ?_)
  simpa using norm_real_sub_ge_abs_im x ζ

/-! ## Positivity of the threshold for `n ≥ 3` -/

/-- For `n ≥ 3`, a primitive `n`-th root of unity is not real. (`±1` are the only
real roots of unity, of orders `1` and `2`.) -/
theorem not_isReal_of_isPrimitiveRoot {n : ℕ} (hn : 3 ≤ n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) : ζ.im ≠ 0 := by
  intro him
  -- `ζ` is real with `‖ζ‖ = 1`, hence `ζ = 1` or `ζ = -1`.
  have hnorm : ‖ζ‖ = 1 := hζ.norm'_eq_one (by omega)
  have hre : ζ = (ζ.re : ℂ) := Complex.ext rfl (by simp [him])
  have habs : |ζ.re| = 1 := by
    rw [hre] at hnorm
    simpa using hnorm
  rcases abs_eq_one.mp habs with h1 | h1
  · -- `ζ = 1` has order `1`.
    have hζ1 : ζ = 1 := by rw [hre, h1]; norm_num
    have : n ∣ 1 := hζ.dvd_of_pow_eq_one 1 (by rw [hζ1]; norm_num)
    omega
  · -- `ζ = -1` has order `2`.
    have hζ1 : ζ = -1 := by rw [hre, h1]; norm_num
    have : n ∣ 2 := hζ.dvd_of_pow_eq_one 2 (by rw [hζ1]; norm_num)
    interval_cases n <;> omega

/-- For `n ≥ 3` the real-axis threshold is strictly positive. -/
theorem imProd_pos {n : ℕ} (hn : 3 ≤ n) : 0 < imProd n := by
  refine Finset.prod_pos (fun ζ hζ => ?_)
  rw [mem_primitiveRoots (by omega : 0 < n)] at hζ
  exact abs_pos.mpr (not_isReal_of_isPrimitiveRoot hn hζ)

/-! ## Disconnection of the sublevel set -/

/-- **Real-axis avoidance.** If `C ≤ imProd n`, no point of the real axis lies in the
sublevel set `{z : ‖Φ_n(z)‖ < C}`. -/
theorem sublevel_avoids_real {n : ℕ} (hn : n ≠ 0) {C : ℝ} (hC : C ≤ imProd n)
    {z : ℂ} (hz : z.im = 0) : ¬ ‖(cyclotomic n ℂ).eval z‖ < C := by
  have hzre : z = (z.re : ℂ) := Complex.ext rfl (by simp [hz])
  rw [hzre]
  push_neg
  calc C ≤ imProd n := hC
    _ ≤ ‖(cyclotomic n ℂ).eval (z.re : ℂ)‖ := imProd_le_norm_cyclotomic_eval_real n hn z.re

/-- **The cyclotomic sublevel set is disconnected for small `C`.** For `n ≥ 3` and
`0 < C ≤ imProd n`, the set `{z : ‖Φ_n(z)‖ < C}` is not preconnected: it avoids the
real axis but meets both open half-planes (at `ζ = e^{2πi/n}` and `ζ⁻¹ = e^{-2πi/n}`),
which therefore disconnect it. First component-count fact for the cyclotomic labyrinth:
its component count is at least `2` in this regime. -/
theorem cyclotomic_sublevel_not_isPreconnected {n : ℕ} (hn : 3 ≤ n) {C : ℝ}
    (hC0 : 0 < C) (hC : C ≤ imProd n) :
    ¬ IsPreconnected {z : ℂ | ‖(cyclotomic n ℂ).eval z‖ < C} := by
  intro hpc
  set S := {z : ℂ | ‖(cyclotomic n ℂ).eval z‖ < C} with hS
  -- The two open half-planes.
  have hupper : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hlower : IsOpen {z : ℂ | z.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  -- The primitive root `ζ = e^{2πi/n}` and its inverse (= conjugate).
  obtain ⟨ζ, hζ⟩ := Complex.isPrimitiveRoot_exp n (by omega)
  have hθpos : 0 < 2 * Real.pi / n := by positivity
  have hθlt : 2 * Real.pi / n < Real.pi := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ))]
    have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [Real.pi_pos]
  have hζform : ζ = Complex.exp ((2 * Real.pi / n : ℝ) * Complex.I) := by
    congr 1
    push_cast
    ring
  have hζim : ζ.im = Real.sin (2 * Real.pi / n) := by
    rw [hζform, Complex.exp_ofReal_mul_I_im]
  have hζinvform : ζ⁻¹ = Complex.exp (-((2 * Real.pi / n : ℝ) * Complex.I)) := by
    rw [hζform, ← Complex.exp_neg]
  have hζinvim : (ζ⁻¹).im = -Real.sin (2 * Real.pi / n) := by
    have : -((2 * Real.pi / n : ℝ) * Complex.I) = ((-(2 * Real.pi / n) : ℝ) * Complex.I) := by
      push_cast
      ring
    rw [hζinvform, this, Complex.exp_ofReal_mul_I_im, Real.sin_neg]
  have hsin : 0 < Real.sin (2 * Real.pi / n) := Real.sin_pos_of_pos_of_lt_pi hθpos hθlt
  -- Both roots lie in the sublevel set.
  have hζS : ζ ∈ S := by
    have : (cyclotomic n ℂ).IsRoot ζ := (isRoot_cyclotomic_iff (n := n)
      (by exact_mod_cast Nat.pos_of_ne_zero (by omega) : (0 : ℕ) < n) |>.mpr hζ)
    simpa [hS, Set.mem_setOf_eq, this.eq_zero] using hC0
  have hζinvS : ζ⁻¹ ∈ S := by
    have hprim : IsPrimitiveRoot ζ⁻¹ n := hζ.inv
    have : (cyclotomic n ℂ).IsRoot ζ⁻¹ := (isRoot_cyclotomic_iff (n := n)
      (by exact_mod_cast Nat.pos_of_ne_zero (by omega) : (0 : ℕ) < n) |>.mpr hprim)
    simpa [hS, Set.mem_setOf_eq, this.eq_zero] using hC0
  -- The sublevel set avoids the real axis, so the half-planes cover it.
  have hcover : S ⊆ {z : ℂ | 0 < z.im} ∪ {z : ℂ | z.im < 0} := by
    intro z hzS
    rcases lt_trichotomy z.im 0 with h | h | h
    · exact Or.inr h
    · exact absurd hzS (sublevel_avoids_real (by omega) hC h)
    · exact Or.inl h
  -- Apply preconnectedness to the separating pair.
  obtain ⟨z, hzS, hz1, hz2⟩ := hpc _ _ hupper hlower hcover
    ⟨ζ, hζS, by simp only [Set.mem_setOf_eq]; rw [hζim]; exact hsin⟩
    ⟨ζ⁻¹, hζinvS, by simp only [Set.mem_setOf_eq]; rw [hζinvim]; linarith⟩
  simp only [Set.mem_setOf_eq] at hz1 hz2
  linarith

#check @norm_real_sub_ge_abs_im
#check @imProd_le_norm_cyclotomic_eval_real
#check @not_isReal_of_isPrimitiveRoot
#check @imProd_pos
#check @sublevel_avoids_real
#check @cyclotomic_sublevel_not_isPreconnected

end CyclotomicPolynomialsOQ02OQ10
