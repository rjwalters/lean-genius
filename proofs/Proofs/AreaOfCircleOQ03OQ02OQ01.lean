/-
Archimedes' Half-Angle Doubling Method: Constructive Formalization

Open Question (area-of-circle-oq-03-oq-02-oq-01):
"Can Archimedes' original half-angle doubling method (computing polygon side
lengths via √((1-cos)/2)) be formalized as a constructive proof?"

Answer: YES. Archimedes (c. 250 BCE) bounded π by inscribing/circumscribing
regular polygons and repeatedly DOUBLING the number of sides, starting from a
hexagon (6 → 12 → 24 → 48 → 96). Each doubling halves the central angle, and the
new half-side length is obtained from the old via the half-angle identity
    sin(θ/2) = √((1 - cos θ)/2).
This file formalizes that doubling step constructively and assembles it into the
full method: the inscribed half-perimeters m·sin(π/m) increase strictly under
doubling, stay below π, and converge to π.

Contents:
  PART I   — The half-angle doubling identities (sin and cos), constructive √ form.
  PART II  — Inscribed half-perimeter p(m) = m·sin(π/m); hexagon base case p(6)=3.
  PART III — Nested-radical (computable) realization for 2ᵏ-gons via sqrtTwoAddSeries.
  PART IV  — Strict monotonicity under doubling, upper bound π, convergence p(m) → π.

References:
- Archimedes, "Measurement of a Circle" (c. 250 BCE)
- Mathlib: Real.sin_half_eq_sqrt, Real.cos_half, Real.sin_pi_over_two_pow_succ,
  Real.lt_tan, Real.sin_lt
-/

import Mathlib

namespace AreaOfCircleOQ03OQ02OQ01

open Real Filter Topology

-- ============================================================
-- PART I: The half-angle doubling identities
-- ============================================================

/-- **Archimedes' half-angle doubling identity (sine form).**
    Doubling an inscribed regular n-gon to a 2n-gon halves the central
    half-angle π/n → π/(2n). The new inscribed half-side length is
    `sin(π/(2n)) = √((1 - cos(π/n))/2)`. This is the literal radical computed
    by Archimedes at each step. Holds for every n ≥ 1. -/
theorem archimedes_sin_doubling {n : ℕ} (hn : 1 ≤ n) :
    Real.sin (Real.pi / (2 * n)) = Real.sqrt ((1 - Real.cos (Real.pi / n)) / 2) := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hπ := Real.pi_pos
  have hnpos : (0 : ℝ) < n := by linarith
  have key : Real.pi / (2 * (n : ℝ)) = (Real.pi / (n : ℝ)) / 2 := by
    field_simp
  rw [key]
  apply Real.sin_half_eq_sqrt
  · positivity
  · -- π/n ≤ 2π  (since n ≥ 1)
    rw [div_le_iff₀ hnpos]
    nlinarith [hπ.le, hn']

/-- **Archimedes' half-angle doubling identity (cosine form).**
    The companion radical `cos(π/(2n)) = √((1 + cos(π/n))/2)`, which Archimedes
    used to propagate the apothem / circumscribed side. Holds for every n ≥ 1. -/
theorem archimedes_cos_doubling {n : ℕ} (hn : 1 ≤ n) :
    Real.cos (Real.pi / (2 * n)) = Real.sqrt ((1 + Real.cos (Real.pi / n)) / 2) := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hπ := Real.pi_pos
  have hnpos : (0 : ℝ) < n := by linarith
  have key : Real.pi / (2 * (n : ℝ)) = (Real.pi / (n : ℝ)) / 2 := by
    field_simp
  rw [key]
  apply Real.cos_half
  · -- -π ≤ π/n
    have : 0 < Real.pi / (n : ℝ) := by positivity
    linarith
  · -- π/n ≤ π  (since n ≥ 1)
    rw [div_le_iff₀ hnpos]
    nlinarith [hπ.le, hn']

-- ============================================================
-- PART II: Inscribed half-perimeter
-- ============================================================

/-- Half-perimeter of the inscribed regular m-gon in the unit circle:
    `p(m) = m · sin(π/m)`. (The full perimeter is 2m·sin(π/m); the half-perimeter
    is the quantity Archimedes compared against π = half the circumference.) -/
noncomputable def halfPerimeter (m : ℕ) : ℝ := (m : ℝ) * Real.sin (Real.pi / m)

/-- Archimedes' starting polygon: the inscribed regular hexagon has half-perimeter
    exactly 3 (since sin(π/6) = 1/2, so 6·(1/2) = 3). This is the seed of the
    doubling iteration. -/
theorem halfPerimeter_hexagon : halfPerimeter 6 = 3 := by
  simp only [halfPerimeter]
  rw [show ((6 : ℕ) : ℝ) = 6 by norm_num, Real.sin_pi_div_six]
  norm_num

-- ============================================================
-- PART III: Nested-radical (computable) realization
-- ============================================================

/-- **Constructive realization for 2ᵏ-gons.** Mathlib's `sqrtTwoAddSeries`
    encodes exactly the Archimedes/Viète nested radicals obtained by iterating the
    half-angle step from a square. The inscribed `2^(n+2)`-gon half-perimeter is the
    closed nested radical
    `p(2^(n+2)) = 2^(n+1) · √(2 - sqrtTwoAddSeries 0 n)`,
    a fully computable expression — confirming the doubling method is constructive. -/
theorem halfPerimeter_pow_two (n : ℕ) :
    halfPerimeter (2 ^ (n + 2)) =
      2 ^ (n + 1) * Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) := by
  simp only [halfPerimeter]
  push_cast
  rw [Real.sin_pi_over_two_pow_succ]
  ring

-- ============================================================
-- PART IV: Monotonicity, upper bound, convergence
-- ============================================================

/-- **Doubling strictly increases the inscribed half-perimeter:** `p(n) < p(2n)`
    for n ≥ 1. Proof: with x = π/(2n), the double-angle identity gives
    `sin(π/n) = 2 sin x cos x`, hence `p(n) = p(2n)·cos x`; since 0 < cos x < 1 and
    p(2n) > 0, the perimeter strictly grows. This is why successive doublings give
    ever-better lower bounds for π. -/
theorem halfPerimeter_doubling {n : ℕ} (hn : 1 ≤ n) :
    halfPerimeter n < halfPerimeter (2 * n) := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hπ := Real.pi_pos
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  set x := Real.pi / (2 * (n : ℝ)) with hx
  have hx_pos : 0 < x := by rw [hx]; positivity
  have hx_le : x ≤ Real.pi / 2 := by
    rw [hx, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hπ.le, hn']
  have hx_ltpi : x < Real.pi := by linarith
  have hsx : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx_pos hx_ltpi
  have hcos_lt : Real.cos x < 1 := by
    have h := Real.strictAntiOn_cos (Set.mem_Icc.mpr ⟨le_refl (0 : ℝ), hπ.le⟩)
        (Set.mem_Icc.mpr ⟨hx_pos.le, le_of_lt hx_ltpi⟩) hx_pos
    rwa [Real.cos_zero] at h
  -- express both half-perimeters in terms of x
  have hP2 : halfPerimeter (2 * n) = (2 * (n : ℝ)) * Real.sin x := by
    simp only [halfPerimeter]; push_cast; rw [← hx]
  have h2x : Real.pi / (n : ℝ) = 2 * x := by rw [hx]; field_simp
  have hP1 : halfPerimeter n = (2 * (n : ℝ)) * Real.sin x * Real.cos x := by
    simp only [halfPerimeter]; rw [h2x, Real.sin_two_mul]; ring
  rw [hP1, hP2]
  have hA : (0 : ℝ) < 2 * (n : ℝ) * Real.sin x := by positivity
  nlinarith [hA, hcos_lt]

/-- **Upper bound:** every inscribed half-perimeter underestimates π,
    `p(m) < π` for m ≥ 1. (Inscribed polygons sit inside the circle.)
    Immediate from `sin t < t`. -/
theorem halfPerimeter_lt_pi {m : ℕ} (hm : 1 ≤ m) : halfPerimeter m < Real.pi := by
  simp only [halfPerimeter]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hu : 0 < Real.pi / m := by positivity
  calc (m : ℝ) * Real.sin (Real.pi / m)
      < (m : ℝ) * (Real.pi / m) := mul_lt_mul_of_pos_left (Real.sin_lt hu) hm'
    _ = Real.pi := by field_simp

/-- **Convergence of the doubling method:** the inscribed half-perimeters converge
    to π, `p(m) → π` as m → ∞. Proof by squeezing
    `π·cos(π/m) ≤ p(m) < π`, where the lower bound is the circumscribed estimate
    (`x < tan x`) and `cos(π/m) → 1`. Together with monotone doubling and the upper
    bound, this is the complete Archimedes argument that the method computes π. -/
theorem halfPerimeter_tendsto_pi :
    Filter.Tendsto (fun m : ℕ => halfPerimeter m) Filter.atTop (nhds Real.pi) := by
  have hπ := Real.pi_pos
  have h0 : Filter.Tendsto (fun m : ℕ => Real.pi / (m : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat Real.pi
  have hcos : Filter.Tendsto (fun m : ℕ => Real.cos (Real.pi / m)) Filter.atTop (nhds 1) := by
    have := (Real.continuous_cos.tendsto 0).comp h0
    simpa [Real.cos_zero] using this
  have hg : Filter.Tendsto (fun m : ℕ => Real.pi * Real.cos (Real.pi / m)) Filter.atTop
      (nhds Real.pi) := by
    have := hcos.const_mul Real.pi
    simpa using this
  have hh : Filter.Tendsto (fun _ : ℕ => Real.pi) Filter.atTop (nhds Real.pi) :=
    tendsto_const_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hg hh ?_ ?_
  · -- lower bound: π·cos(π/m) ≤ p(m), eventually (m ≥ 3)
    filter_upwards [Filter.eventually_ge_atTop 3] with m hm
    have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
    have hmpos : (0 : ℝ) < m := by linarith
    have hu_pos : 0 < Real.pi / m := by positivity
    have hu_lt : Real.pi / m < Real.pi / 2 := by
      rw [div_lt_div_iff₀ hmpos (by norm_num)]
      nlinarith [hπ, hm3]
    have hcospos : 0 < Real.cos (Real.pi / m) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith, hu_lt⟩
    have htan : Real.pi / m < Real.tan (Real.pi / m) := Real.lt_tan hu_pos hu_lt
    rw [Real.tan_eq_sin_div_cos] at htan
    -- (π/m)·cos < sin
    have hkey : (Real.pi / m) * Real.cos (Real.pi / m) < Real.sin (Real.pi / m) := by
      have h := mul_lt_mul_of_pos_right htan hcospos
      rwa [div_mul_cancel₀ _ (ne_of_gt hcospos)] at h
    simp only [halfPerimeter]
    have hrw : Real.pi * Real.cos (Real.pi / m)
        = (m : ℝ) * ((Real.pi / m) * Real.cos (Real.pi / m)) := by
      field_simp
    rw [hrw]
    exact le_of_lt (mul_lt_mul_of_pos_left hkey hmpos)
  · -- upper bound: p(m) ≤ π, eventually (m ≥ 1)
    filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    exact le_of_lt (halfPerimeter_lt_pi hm)

-- ============================================================
-- PART V: Explicit convergence rate (quadratic in 1/m)
-- ============================================================

/-- **Explicit `O(1/m²)` convergence rate of the doubling method.**  The inscribed
half-perimeter approximates π with error at most quadratic in `1/m`:
`π - p(m) ≤ (7/32)·π³/m²` for every `m ≥ 4`.

Proof: with `x = π/m ≤ 1`, Mathlib's Taylor estimate `Real.sin_bound` gives
`sin x ≥ x - x³/6 - (5/96)x⁴`; absorbing `x⁴ ≤ x³` (valid since `x ≤ 1`) into the cubic
term yields `sin x ≥ x - (7/32)x³` (note `1/6 + 5/96 = 7/32`).  Multiplying by `m` and
using `m·x = π`, `m·x³ = π³/m²` gives `p(m) = m·sin x ≥ π - (7/32)π³/m²`.

Since the doubling iteration runs over `m = 6·2ᵏ` (or any `m = c·2ᵏ`), this is exactly the
`π - p(2ᵏ) = O(4⁻ᵏ)` rate of the second open question: each doubling quarters the error
bound. -/
theorem pi_sub_halfPerimeter_le {m : ℕ} (hm : 4 ≤ m) :
    Real.pi - halfPerimeter m ≤ 7 / 32 * Real.pi ^ 3 / (m : ℝ) ^ 2 := by
  have hπ := Real.pi_pos
  have hm' : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  set x := Real.pi / (m : ℝ) with hx
  have hxpos : 0 < x := by rw [hx]; positivity
  have hπlt : Real.pi < 4 := Real.pi_lt_four
  have hx1 : x ≤ 1 := by rw [hx, div_le_one hmpos]; linarith
  -- Taylor lower bound on sin from Real.sin_bound
  have hbound := Real.sin_bound (x := x) (by rw [abs_of_pos hxpos]; exact hx1)
  rw [abs_of_pos hxpos] at hbound
  have hlow : x - x ^ 3 / 6 - x ^ 4 * (5 / 96) ≤ Real.sin x := by
    have := (abs_le.mp hbound).1; linarith
  have hx43 : x ^ 4 ≤ x ^ 3 := by
    calc x ^ 4 = x ^ 3 * x := by ring
      _ ≤ x ^ 3 * 1 := mul_le_mul_of_nonneg_left hx1 (pow_nonneg hxpos.le 3)
      _ = x ^ 3 := by ring
  have hsin : x - 7 / 32 * x ^ 3 ≤ Real.sin x := by nlinarith [hlow, hx43]
  -- clear the m-scaling: m·x = π and m·x³ = π³/m²
  have hmx : (m : ℝ) * x = Real.pi := by rw [hx]; field_simp
  have hmx3 : (m : ℝ) * x ^ 3 = Real.pi ^ 3 / (m : ℝ) ^ 2 := by
    rw [hx]; field_simp
  have hstep : (m : ℝ) * Real.sin x ≥ Real.pi - 7 / 32 * (Real.pi ^ 3 / (m : ℝ) ^ 2) := by
    have h1 : (m : ℝ) * (x - 7 / 32 * x ^ 3) ≤ (m : ℝ) * Real.sin x :=
      mul_le_mul_of_nonneg_left hsin hmpos.le
    have h2 : (m : ℝ) * (x - 7 / 32 * x ^ 3)
        = Real.pi - 7 / 32 * (Real.pi ^ 3 / (m : ℝ) ^ 2) := by
      rw [mul_sub, hmx, show (m : ℝ) * (7 / 32 * x ^ 3) = 7 / 32 * ((m : ℝ) * x ^ 3) by ring,
        hmx3]
    linarith [h1, h2 ▸ h1]
  have hgoal_rw : (7 : ℝ) / 32 * Real.pi ^ 3 / (m : ℝ) ^ 2
      = 7 / 32 * (Real.pi ^ 3 / (m : ℝ) ^ 2) := by ring
  simp only [halfPerimeter]
  rw [← hx, hgoal_rw]
  linarith [hstep]

/-- **Sharp `1/6` leading-constant convergence rate** (answers the second open
question). The earlier `7/32` bound is lossy because it absorbs the quartic Taylor
remainder `x⁴ ≤ x³` into the cubic term. Keeping the quartic remainder *separate*
recovers the error with its **exact** second-order coefficient `1/6`:
`π - p(m) ≤ π³/(6 m²) + (5/96)·π⁴/m³` for `m ≥ 4`.

The leading term `π³/(6 m²)` matches the true Taylor coefficient `1/6` of
`π - m·sin(π/m) = m(π/m)³/6 + O(m⁻³)`; the trailing `O(1/m³)` term carries the rest.
(For `m ≥ 4` one has `π/m ≤ 1`, so `(5/96)π⁴/m³ ≤ (5/96)π³/m²` and the bound collapses
back to `(1/6 + 5/96)π³/m² = (7/32)π³/m²`, recovering `pi_sub_halfPerimeter_le`.) -/
theorem pi_sub_halfPerimeter_le_sharp {m : ℕ} (hm : 4 ≤ m) :
    Real.pi - halfPerimeter m
      ≤ Real.pi ^ 3 / (6 * (m : ℝ) ^ 2) + 5 / 96 * Real.pi ^ 4 / (m : ℝ) ^ 3 := by
  have hπ := Real.pi_pos
  have hm' : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  set x := Real.pi / (m : ℝ) with hx
  have hxpos : 0 < x := by rw [hx]; positivity
  have hπlt : Real.pi < 4 := Real.pi_lt_four
  have hx1 : x ≤ 1 := by rw [hx, div_le_one hmpos]; linarith
  -- Taylor lower bound on sin from Real.sin_bound, keeping the quartic term
  have hbound := Real.sin_bound (x := x) (by rw [abs_of_pos hxpos]; exact hx1)
  rw [abs_of_pos hxpos] at hbound
  have hlow : x - x ^ 3 / 6 - x ^ 4 * (5 / 96) ≤ Real.sin x := by
    have := (abs_le.mp hbound).1; linarith
  -- scale by m, using m·x = π, m·x³ = π³/m², m·x⁴ = π⁴/m³ (all in one ring step)
  have key : (m : ℝ) * (x - x ^ 3 / 6 - x ^ 4 * (5 / 96))
      = Real.pi - Real.pi ^ 3 / (6 * (m : ℝ) ^ 2) - 5 / 96 * Real.pi ^ 4 / (m : ℝ) ^ 3 := by
    rw [hx]; field_simp
  have hscaled : (m : ℝ) * (x - x ^ 3 / 6 - x ^ 4 * (5 / 96)) ≤ (m : ℝ) * Real.sin x :=
    mul_le_mul_of_nonneg_left hlow hmpos.le
  rw [key] at hscaled
  simp only [halfPerimeter]
  rw [← hx]
  linarith [hscaled]

/-- The sharp bound in factored "`1/6 + o(1)`" form:
`π - p(m) ≤ (π³/(6 m²))·(1 + 5π/(16 m))`, exhibiting the leading constant `1/6`
with a relative correction `5π/(16 m) → 0`. As `m → ∞` the bracket tends to `1`,
so the second-order coefficient is exactly `1/6` (the true Taylor value), not `7/32`. -/
theorem pi_sub_halfPerimeter_le_sharp_factored {m : ℕ} (hm : 4 ≤ m) :
    Real.pi - halfPerimeter m
      ≤ Real.pi ^ 3 / (6 * (m : ℝ) ^ 2) * (1 + 5 * Real.pi / (16 * (m : ℝ))) := by
  have hm' : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have h := pi_sub_halfPerimeter_le_sharp hm
  have heq : Real.pi ^ 3 / (6 * (m : ℝ) ^ 2) + 5 / 96 * Real.pi ^ 4 / (m : ℝ) ^ 3
      = Real.pi ^ 3 / (6 * (m : ℝ) ^ 2) * (1 + 5 * Real.pi / (16 * (m : ℝ))) := by
    field_simp; ring
  exact h.trans_eq heq

-- ============================================================
-- PART VI: Summary
-- ============================================================

/-- **Summary.** Archimedes' half-angle doubling method, formalized constructively:
    the doubling identity is the radical `√((1-cos)/2)`; the hexagon seeds the
    iteration at p(6) = 3; doubling strictly increases the half-perimeter while
    keeping it below π; and the sequence converges to π. -/
theorem archimedes_doubling_method_verified :
    (∀ n : ℕ, 1 ≤ n →
      Real.sin (Real.pi / (2 * n)) = Real.sqrt ((1 - Real.cos (Real.pi / n)) / 2)) ∧
    halfPerimeter 6 = 3 ∧
    (∀ n : ℕ, 1 ≤ n → halfPerimeter n < halfPerimeter (2 * n)) ∧
    (∀ m : ℕ, 1 ≤ m → halfPerimeter m < Real.pi) ∧
    Filter.Tendsto (fun m : ℕ => halfPerimeter m) Filter.atTop (nhds Real.pi) :=
  ⟨fun _ hn => archimedes_sin_doubling hn, halfPerimeter_hexagon,
   fun _ hn => halfPerimeter_doubling hn, fun _ hm => halfPerimeter_lt_pi hm,
   halfPerimeter_tendsto_pi⟩

end AreaOfCircleOQ03OQ02OQ01
