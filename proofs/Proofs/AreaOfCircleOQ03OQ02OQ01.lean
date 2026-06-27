/-
  Archimedes' Half-Angle Doubling Method (constructive side-length recurrence)
  Open Question: area-of-circle-oq-03-oq-02-oq-01

  "Can Archimedes' original half-angle doubling method (computing polygon side
   lengths via √((1-cos)/2)) be formalized as a constructive proof?"

  ## Answer: YES.

  Archimedes computed π not from areas but from *perimeters* of inscribed
  regular polygons, doubling the number of sides at each step (6 → 12 → 24 →
  48 → 96). The engine is the half-angle chord identity: the side of the
  2n-gon is obtained from the side of the n-gon by a fixed sequence of square
  roots, so each new side length is *constructible* from the previous one.

  For a unit circle, the side of the regular inscribed n-gon is

      sideLength n = 2 · sin(π/n)

  (a chord subtending central angle 2π/n). The doubling recurrence is the
  nested radical

      sideLength (2n) = √( 2 − √( 4 − sideLength(n)² ) )         (n ≥ 2)

  which is exactly Archimedes' √((1-cos)/2) construction unwound:

      4 − s²  = 4 cos²(π/n)        ⇒  √(4 − s²) = 2 cos(π/n)
      2 − 2cos(π/n) = (2 sin(π/(2n)))²   (half-angle)  ⇒  √(…) = 2 sin(π/(2n)).

  Starting from the hexagon (sideLength 6 = 1) this gives the classical chain
      sideLength 12 = √(2 − √3),   sideLength 24 = √(2 − √(2 + √3)),  …
  and the perimeters n · sideLength n increase to the circumference 2π.

  ## What this file proves (0 sorries, 0 axioms)

  Half-angle infrastructure:
  - sin_sq_half        : sin(x/2)² = (1 − cos x)/2                     (all x)
  - sin_half_eq_sqrt   : sin(x/2) = √((1 − cos x)/2)        (0 ≤ x ≤ 2π)

  The constructive recurrence:
  - sideLength_doubling   : sideLength (2n) = √(2 − √(4 − sideLength(n)²))  (n ≥ 2)
  - sideLength_hexagon    : sideLength 6 = 1
  - sideLength_dodecagon  : sideLength 12 = √(2 − √3)
  - sideLength_pos        : 0 < sideLength n                          (n ≥ 2)

  Convergence (the perimeters reach the circumference):
  - perimeter_lt_two_pi   : perimeter n < 2π                          (n ≥ 2)
  - perimeter_tendsto     : perimeter n → 2π as n → ∞

  ## References
  - Archimedes, "Measurement of a Circle" (c. 250 BCE)
  - Standard nested-radical recurrence for π via inscribed perimeters
-/

import Mathlib

namespace AreaOfCircleOQ03OQ02OQ01

open Real Filter Topology

noncomputable section

/- ## Part 0: Half-angle infrastructure -/

/-- Power-reduction / half-angle identity: `sin(x/2)² = (1 − cos x)/2`.
    Valid for all real `x`. This is the algebraic core of Archimedes' method. -/
theorem sin_sq_half (x : ℝ) : Real.sin (x / 2) ^ 2 = (1 - Real.cos x) / 2 := by
  have h : Real.cos x = 2 * Real.cos (x / 2) ^ 2 - 1 := by
    have := Real.cos_two_mul (x / 2)
    rwa [show 2 * (x / 2) = x from by ring] at this
  have hpyth := Real.sin_sq_add_cos_sq (x / 2)
  linarith [h, hpyth]

/-- Archimedes' square-root form of the half-angle identity:
    `sin(x/2) = √((1 − cos x)/2)` whenever `0 ≤ x ≤ 2π` (so `sin(x/2) ≥ 0`). -/
theorem sin_half_eq_sqrt (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 2 * Real.pi) :
    Real.sin (x / 2) = Real.sqrt ((1 - Real.cos x) / 2) := by
  have hnn : 0 ≤ Real.sin (x / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  rw [← sin_sq_half x, Real.sqrt_sq hnn]

/- ## Part 1: Inscribed polygon side lengths -/

/-- Side length of the regular `n`-gon inscribed in the unit circle:
    a chord subtending central angle `2π/n`, hence `2·sin(π/n)`. -/
noncomputable def sideLength (n : ℕ) : ℝ := 2 * Real.sin (Real.pi / n)

/-- The perimeter of the inscribed regular `n`-gon (unit circle). -/
noncomputable def perimeter (n : ℕ) : ℝ := n * sideLength n

/-- The inscribed side length is positive for `n ≥ 2`
    (then `0 < π/n < π`, so `sin(π/n) > 0`). -/
theorem sideLength_pos (n : ℕ) (hn : 2 ≤ n) : 0 < sideLength n := by
  unfold sideLength
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h_pos : 0 < Real.pi / n := div_pos Real.pi_pos hn0
  have h_lt : Real.pi / n < Real.pi := by
    rw [div_lt_iff₀ hn0]
    nlinarith [Real.pi_pos, (by exact_mod_cast hn : (2 : ℝ) ≤ n)]
  have := Real.sin_pos_of_pos_of_lt_pi h_pos h_lt
  linarith

/-- The hexagon base case: `sideLength 6 = 1` (since `2·sin(π/6) = 2·½ = 1`).
    This is Archimedes' starting point. -/
theorem sideLength_hexagon : sideLength 6 = 1 := by
  unfold sideLength
  rw [show ((6 : ℕ) : ℝ) = 6 from by norm_num, Real.sin_pi_div_six]
  norm_num

/-- **Archimedes' doubling recurrence.**

    The side of the `2n`-gon is built from the side of the `n`-gon by the nested
    radical `√(2 − √(4 − s²))`. Each new side is constructible (a finite tower of
    square roots) from the previous one — the precise sense in which Archimedes'
    half-angle method is *constructive*.

    Requires `n ≥ 2` so that `cos(π/n) ≥ 0` (the doubling stays in the first
    quadrant), which is satisfied at every step of the classical 6→12→24→… chain. -/
theorem sideLength_doubling (n : ℕ) (hn : 2 ≤ n) :
    sideLength (2 * n) = Real.sqrt (2 - Real.sqrt (4 - (sideLength n) ^ 2)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have ha_pos : 0 < Real.pi / n := div_pos Real.pi_pos hn0
  -- π/n ≤ π/2  (since n ≥ 2): keeps the half-angle in the first quadrant
  have ha_le : Real.pi / n ≤ Real.pi / 2 := by
    gcongr
    exact_mod_cast hn
  have hcos_nn : 0 ≤ Real.cos (Real.pi / n) :=
    Real.cos_nonneg_of_mem_Icc (Set.mem_Icc.mpr ⟨by linarith [ha_pos, Real.pi_pos], ha_le⟩)
  -- LHS:  sideLength (2n) = 2 · sin(π/(2n)) = 2 · sin((π/n)/2)
  have hcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hLHS : sideLength (2 * n) = 2 * Real.sin (Real.pi / n / 2) := by
    unfold sideLength
    rw [hcast, show Real.pi / (2 * (n : ℝ)) = Real.pi / n / 2 from by ring]
  rw [hLHS]
  -- inner radical:  4 − sideLength(n)² = (2 cos(π/n))²
  have hsq : (sideLength n) ^ 2 = 4 * Real.sin (Real.pi / n) ^ 2 := by
    unfold sideLength; ring
  have hinner : 4 - (sideLength n) ^ 2 = (2 * Real.cos (Real.pi / n)) ^ 2 := by
    rw [hsq]; nlinarith [Real.sin_sq_add_cos_sq (Real.pi / n)]
  rw [hinner, Real.sqrt_sq (by linarith [hcos_nn] : (0 : ℝ) ≤ 2 * Real.cos (Real.pi / n))]
  -- outer radical:  2 − 2cos(π/n) = (2 sin((π/n)/2))²  via the half-angle identity
  have houter : 2 - 2 * Real.cos (Real.pi / n) = (2 * Real.sin (Real.pi / n / 2)) ^ 2 := by
    nlinarith [sin_sq_half (Real.pi / n)]
  have hpos : 0 ≤ 2 * Real.sin (Real.pi / n / 2) := by
    have : 0 ≤ Real.sin (Real.pi / n / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
        (by linarith [ha_le, Real.pi_pos])
    linarith
  rw [houter, Real.sqrt_sq hpos]

/-- The first doubling step from the hexagon: `sideLength 12 = √(2 − √3)`.
    (`4 − 1² = 3`.) A concrete instance of the constructive recurrence. -/
theorem sideLength_dodecagon : sideLength 12 = Real.sqrt (2 - Real.sqrt 3) := by
  have h : sideLength 12 = Real.sqrt (2 - Real.sqrt (4 - (sideLength 6) ^ 2)) := by
    have := sideLength_doubling 6 (by norm_num)
    simpa using this
  rw [h, sideLength_hexagon]
  norm_num

/- ## Part 2: Convergence of perimeters to the circumference 2π -/

/-- Each inscribed perimeter underestimates the circumference: `perimeter n < 2π`
    for `n ≥ 2` (Archimedes' lower-bound side), since `sin(π/n) < π/n`. -/
theorem perimeter_lt_two_pi (n : ℕ) (hn : 2 ≤ n) : perimeter n < 2 * Real.pi := by
  unfold perimeter sideLength
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hn0
  have hp : 0 < Real.pi / n := div_pos Real.pi_pos hn0
  have hlt : Real.sin (Real.pi / n) < Real.pi / n := Real.sin_lt hp
  calc (n : ℝ) * (2 * Real.sin (Real.pi / n))
      < (n : ℝ) * (2 * (Real.pi / n)) := by
        apply mul_lt_mul_of_pos_left _ hn0; linarith
    _ = 2 * Real.pi := by field_simp; ring

/-- `sin(h)/h → 1` as `h → 0` through nonzero values
    (the derivative of `sin` at `0` is `cos 0 = 1`). -/
theorem tendsto_sin_div_nhds_zero :
    Filter.Tendsto (fun h : ℝ => Real.sin h / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1) := by
  have hd : HasDerivAt Real.sin 1 0 := by
    have := Real.hasDerivAt_sin 0
    rw [Real.cos_zero] at this
    exact this
  rw [hasDerivAt_iff_tendsto_slope] at hd
  exact hd.congr' (Filter.Eventually.of_forall (fun y => by
    simp [slope_def_field, Real.sin_zero]))

/-- `π/n → 0` through nonzero values as `n → ∞`. -/
theorem tendsto_pi_div_atTop :
    Filter.Tendsto (fun n : ℕ => Real.pi / n)
      Filter.atTop (nhdsWithin 0 {(0 : ℝ)}ᶜ) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨tendsto_const_div_atTop_nhds_0_nat _, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact Set.mem_compl_singleton_iff.mpr
    (div_ne_zero (by positivity) (Nat.cast_ne_zero.mpr (by omega)))

/-- `sin(π/n)/(π/n) → 1` as `n → ∞` (composition of the two limits above). -/
theorem tendsto_sin_pi_div_n :
    Filter.Tendsto (fun n : ℕ => Real.sin (Real.pi / n) / (Real.pi / n))
      Filter.atTop (nhds 1) :=
  tendsto_sin_div_nhds_zero.comp tendsto_pi_div_atTop

/-- `n · sin(π/n) → π` as `n → ∞`. -/
theorem tendsto_n_sin_pi_div_n :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) * Real.sin (Real.pi / n))
      Filter.atTop (nhds Real.pi) := by
  have key : ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) * Real.sin (Real.pi / n) =
      Real.pi * (Real.sin (Real.pi / n) / (Real.pi / n)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
    ring
  have h_mul : Filter.Tendsto
      (fun n : ℕ => Real.pi * (Real.sin (Real.pi / n) / (Real.pi / n)))
      Filter.atTop (nhds Real.pi) := by
    have := tendsto_sin_pi_div_n.const_mul Real.pi
    simp only [mul_one] at this
    exact this
  exact h_mul.congr' key.symm

/-- **Convergence of Archimedes' method.** The inscribed perimeters converge to
    the circumference of the unit circle:  `perimeter n → 2π` as `n → ∞`.

    Combined with `sideLength_doubling`, this is the full content of the
    half-angle method: the doubling sequence of constructible side lengths
    produces perimeters that reach `2π`, i.e. compute `π`. -/
theorem perimeter_tendsto :
    Filter.Tendsto (fun n : ℕ => perimeter n) Filter.atTop (nhds (2 * Real.pi)) := by
  have h : (fun n : ℕ => perimeter n)
      = (fun n : ℕ => 2 * ((n : ℝ) * Real.sin (Real.pi / n))) := by
    funext n; unfold perimeter sideLength; ring
  rw [h]
  exact tendsto_n_sin_pi_div_n.const_mul 2

end

end AreaOfCircleOQ03OQ02OQ01
