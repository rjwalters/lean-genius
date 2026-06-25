/-
# Hilbert 22 (OQ-01-OQ-03) — Blaschke automorphisms and the pseudohyperbolic gauge

The algebraic backbone of the Schwarz–Pick / Kobayashi program on the unit disk
(Item 3 of the `hilbert-22-oq-01-oq-03` decomposition).

This file is deliberately **elementary**: it works with raw complex numbers under
the hypothesis `‖·‖ < 1` and uses only field algebra over `ℂ` (no holomorphy, no
special functions such as `arctanh`).  Mathlib provides the unit-disc *type*
(`Complex.UnitDisc`) but no Blaschke automorphism, no pseudohyperbolic distance,
and no Schwarz–Pick lemma — this file supplies the foundational identities that
those results are built from.

Main results:

* `blaschke a z = (z - a) / (1 - conj a * z)` — the disk automorphism sending `a ↦ 0`.
* `normSq_oneSubConjMul_sub_normSq_sub` — the Pythagorean identity
  `|1 - ā z|² - |z - a|² = (1 - |a|²)(1 - |z|²)`, the engine of the whole theory.
* `normSq_blaschke_lt_one` / `psh_lt_one` — Blaschke factors map the disk into itself.
* `blaschke_eq_zero_iff`, `psh_self`, `psh_eq_zero_iff`, `psh_comm` — the
  pseudohyperbolic gauge `psh z w = ‖blaschke w z‖` is a symmetric, nonnegative
  separating gauge taking values in `[0, 1)`.  (It is *not* a metric — the genuine
  Poincaré metric is `arctanh ∘ psh`; that requires `arctanh`, absent from Mathlib.)
* `psh_schwarzPick_center` — the center-fixing case of Schwarz–Pick, obtained by
  specialising Mathlib's center-fixing Schwarz lemma; the general two-point form
  reduces to this by Blaschke conjugation, whose algebraic core is the identities above.

These connect to the abstract Kobayashi chain pseudometric of `Hilbert22OQ01OQ03.lean`:
`psh` (after `arctanh`) is the atomic cost whose chain infimum is the Kobayashi metric.
-/
import Mathlib

open Complex Metric Set
open scoped ComplexConjugate

namespace Hilbert22OQ01OQ03

/-- The **Blaschke automorphism** of the unit disk that sends `a` to `0`:
`φ_a(z) = (z - a) / (1 - ā z)`. -/
noncomputable def blaschke (a z : ℂ) : ℂ := (z - a) / (1 - conj a * z)

/-- On the unit disk the Blaschke denominator is nonzero:
`1 - ā z ≠ 0` whenever `‖a‖ < 1` and `‖z‖ < 1`. -/
lemma oneSubConjMul_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    1 - conj a * z ≠ 0 := by
  have hw : ‖conj a * z‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    calc ‖a‖ * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ha.le (norm_nonneg z)
      _ = ‖z‖ := one_mul _
      _ < 1 := hz
  intro hcontra
  have h1 : (1 : ℂ) = conj a * z := sub_eq_zero.mp hcontra
  rw [← h1, norm_one] at hw
  exact lt_irrefl 1 hw

/-- **Pythagorean (Schwarz–Pick) identity.** The numerator gap controlling
`1 - |φ_a(z)|²`:
`|1 - ā z|² - |z - a|² = (1 - |a|²)(1 - |z|²)`.
Pure real-polynomial algebra in the real and imaginary parts. -/
lemma normSq_oneSubConjMul_sub_normSq_sub (a z : ℂ) :
    normSq (1 - conj a * z) - normSq (z - a)
      = (1 - normSq a) * (1 - normSq z) := by
  simp only [normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
  ring

/-- `|1 - w̄ z|² = |1 - z̄ w|²`: the Blaschke denominator is norm-symmetric. -/
lemma normSq_oneSubConjMul_comm (z w : ℂ) :
    normSq (1 - conj w * z) = normSq (1 - conj z * w) := by
  simp only [normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
  ring

/-- A Blaschke factor maps the open unit disk into itself: `|φ_a(z)|² < 1`. -/
lemma normSq_blaschke_lt_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    normSq (blaschke a z) < 1 := by
  have hden : (1 - conj a * z) ≠ 0 := oneSubConjMul_ne_zero ha hz
  have hdenpos : 0 < normSq (1 - conj a * z) := normSq_pos.mpr hden
  have hNa : normSq a < 1 := by
    have h : ‖a‖ ^ 2 < 1 := by nlinarith [norm_nonneg a]
    rwa [Complex.sq_norm] at h
  have hNz : normSq z < 1 := by
    have h : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
    rwa [Complex.sq_norm] at h
  have key := normSq_oneSubConjMul_sub_normSq_sub a z
  have hpos : 0 < (1 - normSq a) * (1 - normSq z) := mul_pos (by linarith) (by linarith)
  have hlt : normSq (z - a) < normSq (1 - conj a * z) := by linarith
  rw [blaschke, map_div₀, div_lt_one hdenpos]
  exact hlt

/-- A Blaschke factor vanishes exactly at its center: `φ_a(z) = 0 ↔ z = a`. -/
lemma blaschke_eq_zero_iff {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    blaschke a z = 0 ↔ z = a := by
  have hden : (1 - conj a * z) ≠ 0 := oneSubConjMul_ne_zero ha hz
  rw [blaschke, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact sub_eq_zero.mp h
    · exact absurd h hden
  · intro h; left; rw [h, sub_self]

/-- `φ_a(a) = 0`. -/
@[simp] lemma blaschke_self (a : ℂ) : blaschke a a = 0 := by
  simp [blaschke]

/-- `φ_0 = id`. -/
@[simp] lemma blaschke_zero_left (z : ℂ) : blaschke 0 z = z := by
  simp [blaschke]

/-- The **pseudohyperbolic gauge** on the unit disk:
`psh z w = |φ_w(z)| = |(z - w) / (1 - w̄ z)|`. -/
noncomputable def psh (z w : ℂ) : ℝ := ‖blaschke w z‖

lemma psh_nonneg (z w : ℂ) : 0 ≤ psh z w := norm_nonneg _

@[simp] lemma psh_self (z : ℂ) : psh z z = 0 := by
  simp [psh]

/-- `psh z 0 = ‖z‖`: at the center the gauge is the Euclidean norm. -/
@[simp] lemma psh_zero_right (z : ℂ) : psh z 0 = ‖z‖ := by
  simp [psh]

/-- The pseudohyperbolic gauge takes values strictly below `1` on the disk. -/
lemma psh_lt_one {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) : psh z w < 1 := by
  rw [psh]
  have h := normSq_blaschke_lt_one hw hz
  have h2 : ‖blaschke w z‖ ^ 2 < 1 := by rwa [Complex.sq_norm]
  nlinarith [norm_nonneg (blaschke w z)]

/-- The gauge separates points: `psh z w = 0 ↔ z = w`. -/
lemma psh_eq_zero_iff {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    psh z w = 0 ↔ z = w := by
  rw [psh, norm_eq_zero, blaschke_eq_zero_iff hw hz]

/-- The gauge is symmetric: `psh z w = psh w z`. -/
lemma psh_comm (z w : ℂ) : psh z w = psh w z := by
  rw [psh, psh, blaschke, blaschke, norm_div, norm_div, norm_sub_rev,
    Complex.norm_def (1 - conj w * z), Complex.norm_def (1 - conj z * w),
    normSq_oneSubConjMul_comm]

/-- **Schwarz–Pick, center case.** A holomorphic self-map of the unit disk fixing
`0` is a pseudohyperbolic contraction toward the center:
`psh (f z) 0 ≤ psh z 0`.

This specialises Mathlib's center-fixing Schwarz lemma
(`Complex.norm_le_norm_of_mapsTo_ball_self`).  The *general* two-point Schwarz–Pick
`psh (f z) (f w) ≤ psh z w` reduces to this case by pre/post-composing with the
Blaschke automorphisms `blaschke w` and `blaschke (f w)`, whose disk-preserving
algebra is exactly `normSq_blaschke_lt_one` and `blaschke_eq_zero_iff` above. -/
lemma psh_schwarzPick_center {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1))
    (hmaps : MapsTo f (ball 0 1) (ball 0 1)) (hf0 : f 0 = 0)
    {z : ℂ} (hz : ‖z‖ < 1) : psh (f z) 0 ≤ psh z 0 := by
  rw [psh_zero_right, psh_zero_right]
  exact Complex.norm_le_norm_of_mapsTo_ball_self hd hmaps hf0 hz

end Hilbert22OQ01OQ03
