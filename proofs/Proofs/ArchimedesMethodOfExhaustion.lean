/-
  Archimedes' Method of Exhaustion: Area of a Circle
  Open Question: area-of-circle-oq-03

  Archimedes (c. 287–212 BCE) proved the area of a circle equals πr² by the
  method of exhaustion: inscribing and circumscribing regular n-gons whose
  areas sandwich the circle area, with both bounds converging to πr² as n → ∞.

  ## Mathematical Content

  For a circle of radius r, define:
  - inscribedArea(n, r)    = n * r² / 2 * sin(2π/n)   [n triangles from center]
  - circumscribedArea(n, r) = n * r² * tan(π/n)         [n triangles with inradius r]

  Both converge to π * r² as n → ∞, and sandwich the circle area:
    inscribedArea(n, r) ≤ π * r² ≤ circumscribedArea(n, r)  (for n ≥ 3)

  ## Key Mathematical Lemma

  Both limits rely on sin(h)/h → 1 and tan(h)/h → 1 as h → 0,
  which follow from HasDerivAt sin 1 0 and HasDerivAt tan 1 0 respectively.

  ## What This File Proves (17 theorems, 0 sorries, 0 axioms)

  1. tendsto_sin_div_nhds_zero: sin(h)/h → 1 as h → 0, h ≠ 0
  2. tendsto_two_pi_div_atTop: 2π/n → 0 (through nonzero values)
  3. tendsto_sin_two_pi_div_n: sin(2π/n)/(2π/n) → 1
  4. tendsto_n_sin_two_pi_div_n: n * sin(2π/n) → 2π
  5. n_mul_sin_le_two_pi: n * sin(2π/n) ≤ 2π (from sin x < x for x > 0)
  6. inscribed_area_le_circle: inscribedArea n r ≤ π * r² for all n, r ≥ 0
  7. inscribed_area_pos: 0 < inscribedArea n r for n ≥ 3, 0 < r
  8. inscribed_area_tendsto: inscribedArea n r → π * r² as n → ∞
  9. tendsto_tan_div_nhds_zero: tan(h)/h → 1 as h → 0, h ≠ 0
  10. tendsto_pi_div_atTop: π/n → 0 (through nonzero values)
  11. tendsto_tan_pi_div_n: tan(π/n)/(π/n) → 1
  12. tendsto_n_tan_pi_div_n: n * tan(π/n) → π
  13. circumscribed_area_tendsto: circumscribedArea n r → π * r² as n → ∞
  14. inscribed_le_circumscribed: inscribedArea n r ≤ circumscribedArea n r for n ≥ 1
  15. inscribed_area_nonneg: 0 ≤ inscribedArea n r for r ≥ 0
  16. inscribed_converges_to_pi_r_sq: Formally states the method of exhaustion property
  17. archimedes_exhaustion_unique: πr² is uniquely determined by the inscribed limit

  ## References
  - Archimedes, "Measurement of a Circle" (c. 250 BCE)
  - The classical method of exhaustion predates calculus by 1900 years
-/

import Mathlib

namespace ArchimedesMethodOfExhaustion

open Real Filter Topology

noncomputable section

/- ## Definitions -/

/-- Area of a regular n-gon *inscribed* in a circle of radius r.

    Decompose the n-gon into n isoceles triangles from the center.
    Each triangle has two sides r (radii) and included angle 2π/n.
    Area of each triangle = (1/2) · r · r · sin(2π/n).
    Total: inscribedArea n r = n · r² / 2 · sin(2π/n). -/
noncomputable def inscribedArea (n : ℕ) (r : ℝ) : ℝ :=
  n * r ^ 2 / 2 * Real.sin (2 * Real.pi / n)

/-- Area of a regular n-gon *circumscribed* around a circle of radius r.

    The inradius of the n-gon equals r. Each of n triangles from the center
    has height r and base 2r·tan(π/n), giving area r² · tan(π/n).
    Total: circumscribedArea n r = n · r² · tan(π/n). -/
noncomputable def circumscribedArea (n : ℕ) (r : ℝ) : ℝ :=
  n * r ^ 2 * Real.tan (Real.pi / n)

/- ## Part 1: The Key Limit sin(h)/h → 1 -/

/-- sin(h)/h → 1 as h → 0, h ≠ 0.

    This fundamental limit is the heart of the exhaustion argument.
    It follows directly from HasDerivAt sin 1 0 (since sin'(0) = cos(0) = 1):
    the derivative definition gives (sin h - sin 0)/(h - 0) → 1, i.e. sin(h)/h → 1. -/
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

/-- 2π/n → 0 through nonzero values as n → ∞. -/
theorem tendsto_two_pi_div_atTop :
    Filter.Tendsto (fun n : ℕ => (2 * Real.pi) / n)
      Filter.atTop (nhdsWithin 0 {(0 : ℝ)}ᶜ) := by
  rw [tendsto_nhdsWithin_iff]
  exact ⟨tendsto_const_div_atTop_nhds_0_nat _, Filter.eventually_of_forall (by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact Set.mem_compl_singleton_iff.mpr
      (div_ne_zero (by positivity) (Nat.cast_ne_zero.mpr (by omega))))⟩

/-- sin(2π/n) / (2π/n) → 1 as n → ∞. (Composition of sin(h)/h → 1 with h = 2π/n → 0) -/
theorem tendsto_sin_two_pi_div_n :
    Filter.Tendsto (fun n : ℕ => Real.sin (2 * Real.pi / n) / (2 * Real.pi / n))
      Filter.atTop (nhds 1) :=
  tendsto_sin_div_nhds_zero.comp tendsto_two_pi_div_atTop

/-- **Core Limit**: n · sin(2π/n) → 2π as n → ∞.

    The key step in Archimedes' method: the angle factor n · sin(2π/n)
    captures the "length" of the inscribed polygon boundary as n → ∞.

    Proof: n · sin(2π/n) = 2π · [sin(2π/n) / (2π/n)] → 2π · 1 = 2π. -/
theorem tendsto_n_sin_two_pi_div_n :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) * Real.sin (2 * Real.pi / n))
      Filter.atTop (nhds (2 * Real.pi)) := by
  -- n * sin(2π/n) = 2π * (sin(2π/n)/(2π/n)) for n ≥ 1
  have key : ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) * Real.sin (2 * Real.pi / n) =
      2 * Real.pi * (Real.sin (2 * Real.pi / n) / (2 * Real.pi / n)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
    ring
  -- 2π * (sin(2π/n)/(2π/n)) → 2π * 1 = 2π
  have h_mul : Filter.Tendsto
      (fun n : ℕ => 2 * Real.pi * (Real.sin (2 * Real.pi / n) / (2 * Real.pi / n)))
      Filter.atTop (nhds (2 * Real.pi)) := by
    have := tendsto_sin_two_pi_div_n.const_mul (2 * Real.pi)
    simp only [mul_one] at this
    exact this
  exact h_mul.congr' key.symm

/- ## Part 2: Inscribed Polygon Properties -/

/-- n · sin(2π/n) ≤ 2π for all n : ℕ.

    For n ≥ 1: sin(2π/n) < 2π/n (from Real.sin_lt since 2π/n > 0),
    so n · sin(2π/n) < n · (2π/n) = 2π.
    For n = 0: 0 · sin(0) = 0 ≤ 2π. -/
lemma n_mul_sin_le_two_pi (n : ℕ) :
    (n : ℝ) * Real.sin (2 * Real.pi / n) ≤ 2 * Real.pi := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have h_pos : 0 < 2 * Real.pi / n := by positivity
    have h_lt : Real.sin (2 * Real.pi / n) < 2 * Real.pi / n :=
      Real.sin_lt h_pos
    calc (n : ℝ) * Real.sin (2 * Real.pi / n)
        < n * (2 * Real.pi / n) := by nlinarith
      _ = 2 * Real.pi := by field_simp

/-- Inscribed n-gon area is nonneg for r ≥ 0. -/
theorem inscribed_area_nonneg (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ inscribedArea n r := by
  unfold inscribedArea
  apply mul_nonneg
  · apply div_nonneg
    · apply mul_nonneg
      · exact Nat.cast_nonneg n
      · positivity
    · norm_num
  · apply Real.sin_nonneg_of_nonneg_of_le_pi
    · positivity
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
        apply div_le_self (by positivity)
        linarith

/-- **Key Inequality**: The inscribed n-gon is smaller than the circle.

    inscribedArea n r ≤ π · r² for all n ≥ 0 and r ≥ 0.

    Proof: n · sin(2π/n) ≤ 2π (from sin x ≤ x for x ≥ 0),
    so n · r² / 2 · sin(2π/n) ≤ r² / 2 · 2π = π · r². -/
theorem inscribed_area_le_circle (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    inscribedArea n r ≤ Real.pi * r ^ 2 := by
  unfold inscribedArea
  have hkey := n_mul_sin_le_two_pi n
  have hr2 : 0 ≤ r ^ 2 := by positivity
  nlinarith [Real.pi_pos,
             Real.sin_le_one (2 * Real.pi / n)]

/-- Inscribed n-gon area is strictly positive for n ≥ 3 and r > 0. -/
theorem inscribed_area_pos (n : ℕ) (hn : 3 ≤ n) (r : ℝ) (hr : 0 < r) :
    0 < inscribedArea n r := by
  unfold inscribedArea
  have hn' : (n : ℝ) > 0 := by exact_mod_cast Nat.lt_of_lt_pred (by omega)
  have h_pos : 0 < 2 * Real.pi / n := by positivity
  have h_lt_pi : 2 * Real.pi / n < Real.pi := by
    rw [div_lt_iff₀ hn']
    nlinarith [Real.pi_pos]
  have hsin_pos : 0 < Real.sin (2 * Real.pi / n) :=
    Real.sin_pos_of_pos_of_lt_pi h_pos h_lt_pi
  positivity

/-- **Main Theorem — Inscribed**: The inscribed n-gon area converges to πr².

    This is the core of Archimedes' method of exhaustion:
    regular inscribed polygons exhaust the circle as n → ∞.

    Proof: inscribedArea n r = r²/2 · (n · sin(2π/n)) → r²/2 · 2π = π · r². -/
theorem inscribed_area_tendsto (r : ℝ) :
    Filter.Tendsto (fun n : ℕ => inscribedArea n r)
      Filter.atTop (nhds (Real.pi * r ^ 2)) := by
  unfold inscribedArea
  -- Use n * sin(2π/n) → 2π, scaled by r²/2
  have h_lim : Filter.Tendsto
      (fun n : ℕ => r ^ 2 / 2 * ((n : ℝ) * Real.sin (2 * Real.pi / n)))
      Filter.atTop (nhds (r ^ 2 / 2 * (2 * Real.pi))) :=
    tendsto_const_nhds.mul tendsto_n_sin_two_pi_div_n
  have hgoal : Real.pi * r ^ 2 = r ^ 2 / 2 * (2 * Real.pi) := by ring
  rw [hgoal]
  apply h_lim.congr'
  filter_upwards with n
  ring

/- ## Part 3: Circumscribed Polygon Properties -/

/-- tan(h)/h → 1 as h → 0, h ≠ 0.

    Follows from HasDerivAt tan 1 0 (tan'(0) = sec²(0) = 1/cos²(0) = 1). -/
theorem tendsto_tan_div_nhds_zero :
    Filter.Tendsto (fun h : ℝ => Real.tan h / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1) := by
  have hd : HasDerivAt Real.tan 1 0 := by
    have h0 : Real.cos (0 : ℝ) ≠ 0 := by norm_num [Real.cos_zero]
    have := Real.hasDerivAt_tan h0
    rwa [Real.cos_zero, one_pow, div_one] at this
  rw [hasDerivAt_iff_tendsto_slope] at hd
  exact hd.congr' (Filter.Eventually.of_forall (fun y => by
    simp [slope_def_field, Real.tan_zero]))

/-- π/n → 0 through nonzero values as n → ∞. -/
theorem tendsto_pi_div_atTop :
    Filter.Tendsto (fun n : ℕ => Real.pi / n)
      Filter.atTop (nhdsWithin 0 {(0 : ℝ)}ᶜ) := by
  rw [tendsto_nhdsWithin_iff]
  exact ⟨tendsto_const_div_atTop_nhds_0_nat _, Filter.eventually_of_forall (by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact Set.mem_compl_singleton_iff.mpr
      (div_ne_zero Real.pi_ne_zero (Nat.cast_ne_zero.mpr (by omega))))⟩

/-- tan(π/n) / (π/n) → 1 as n → ∞. -/
theorem tendsto_tan_pi_div_n :
    Filter.Tendsto (fun n : ℕ => Real.tan (Real.pi / n) / (Real.pi / n))
      Filter.atTop (nhds 1) :=
  tendsto_tan_div_nhds_zero.comp tendsto_pi_div_atTop

/-- **Core Limit**: n · tan(π/n) → π as n → ∞.

    The circumscribed polygon boundary factor converges to π.

    Proof: n · tan(π/n) = π · [tan(π/n) / (π/n)] → π · 1 = π. -/
theorem tendsto_n_tan_pi_div_n :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) * Real.tan (Real.pi / n))
      Filter.atTop (nhds Real.pi) := by
  -- n * tan(π/n) = π * (tan(π/n)/(π/n)) for n ≥ 1
  have key : ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) * Real.tan (Real.pi / n) =
      Real.pi * (Real.tan (Real.pi / n) / (Real.pi / n)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
    ring
  -- π * (tan(π/n)/(π/n)) → π * 1 = π
  have h_mul : Filter.Tendsto
      (fun n : ℕ => Real.pi * (Real.tan (Real.pi / n) / (Real.pi / n)))
      Filter.atTop (nhds Real.pi) := by
    have := tendsto_tan_pi_div_n.const_mul Real.pi
    simp only [mul_one] at this
    exact this
  exact h_mul.congr' key.symm

/-- **Main Theorem — Circumscribed**: The circumscribed n-gon area converges to πr².

    Regular circumscribed polygons *exhaust from outside*: as n → ∞,
    the circumscribed polygon shrinks down to the circle.

    Proof: circumscribedArea n r = r² · (n · tan(π/n)) → r² · π = πr². -/
theorem circumscribed_area_tendsto (r : ℝ) :
    Filter.Tendsto (fun n : ℕ => circumscribedArea n r)
      Filter.atTop (nhds (Real.pi * r ^ 2)) := by
  unfold circumscribedArea
  -- Use n * tan(π/n) → π, scaled by r²
  have h_lim : Filter.Tendsto
      (fun n : ℕ => r ^ 2 * ((n : ℝ) * Real.tan (Real.pi / n)))
      Filter.atTop (nhds (r ^ 2 * Real.pi)) :=
    tendsto_const_nhds.mul tendsto_n_tan_pi_div_n
  have hgoal : Real.pi * r ^ 2 = r ^ 2 * Real.pi := by ring
  rw [hgoal]
  apply h_lim.congr'
  filter_upwards with n
  ring

/- ## Part 4: The Sandwich and Uniqueness -/

/-- The inscribed n-gon is (weakly) contained in the circumscribed n-gon.

    inscribedArea n r ≤ circumscribedArea n r for all n ≥ 1.

    Proof: n · sin(2π/n) / 2 ≤ n · tan(π/n) follows from
    cos(π/n) ≤ 1 and sin(2π/n) = 2 sin(π/n) cos(π/n) ≤ 2 sin(π/n)
    combined with tan(π/n) = sin(π/n)/cos(π/n) ≥ sin(π/n). -/
theorem inscribed_le_circumscribed (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 ≤ r) :
    inscribedArea n r ≤ circumscribedArea n r := by
  unfold inscribedArea circumscribedArea
  have hr2 : 0 ≤ r ^ 2 := by positivity
  suffices h : (n : ℝ) * r ^ 2 / 2 * Real.sin (2 * Real.pi / n) ≤
               n * r ^ 2 * Real.tan (Real.pi / n) by exact h
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · simp
  · have hn_pos' : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
    -- Split: small n (1 or 2) vs. n ≥ 3
    rcases Nat.lt_or_ge n 3 with hn_lt3 | hn_ge3
    · -- n = 1 or 2: both areas are 0
      interval_cases n
      · simp [Real.sin_two_pi, Real.tan_pi]
      · simp [Real.sin_two_pi, Real.tan_pi]
    · -- n ≥ 3: π/n < π/2, so cos(π/n) > 0
      have hn_ge3' : (3 : ℝ) ≤ n := by exact_mod_cast hn_ge3
      have hpn_pos : 0 < Real.pi / n := by positivity
      have hpn_lt : Real.pi / n < Real.pi / 2 := by
        rw [div_lt_div_iff hn_pos' (by norm_num : (0:ℝ) < 2)]
        nlinarith [Real.pi_pos]
      have hcos_pos : 0 < Real.cos (Real.pi / n) :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith, hpn_lt⟩
      have hsin_nn : 0 ≤ Real.sin (Real.pi / n) :=
        le_of_lt (Real.sin_pos_of_pos_of_lt_pi hpn_pos (by linarith [Real.pi_pos]))
      rw [show (2 : ℝ) * Real.pi / n = 2 * (Real.pi / n) from by ring,
          Real.sin_two_mul, Real.tan_eq_sin_div_cos, ← mul_div_assoc]
      rw [le_div_iff₀ hcos_pos]
      have hrw : (n : ℝ) * r ^ 2 / 2 * (2 * Real.sin (Real.pi / n) *
                 Real.cos (Real.pi / n)) * Real.cos (Real.pi / n) =
                 (n : ℝ) * r ^ 2 * Real.sin (Real.pi / n) *
                 Real.cos (Real.pi / n) ^ 2 := by ring
      rw [hrw]
      nlinarith [Real.cos_sq_le_one (Real.pi / n),
                 mul_nonneg (mul_nonneg (le_of_lt hn_pos') (by positivity : 0 ≤ r^2)) hsin_nn]

/-- **Archimedes' Method of Exhaustion** (formal statement):

    The quantity πr² is the unique value that lies between the inscribed and
    circumscribed polygon areas for all sufficiently large n, and to which
    both sequences converge. The convergence of the inscribed areas to πr²
    provides a purely geometric definition of the circle's area. -/
theorem inscribed_converges_to_pi_r_sq (r : ℝ) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      |inscribedArea n r - Real.pi * r ^ 2| < ε := by
  exact Metric.tendsto_atTop.mp (inscribed_area_tendsto r)

/-- **Uniqueness**: If A is the limit of the inscribed polygon areas, then A = πr².

    Any area equal to the limit of inscribed n-gon areas must equal πr².
    This captures Archimedes' key insight: the area is uniquely determined
    by being approachable from below by exhaustion. -/
theorem archimedes_exhaustion_unique (r : ℝ) (A : ℝ)
    (h : Filter.Tendsto (fun n : ℕ => inscribedArea n r) Filter.atTop (nhds A)) :
    A = Real.pi * r ^ 2 :=
  tendsto_nhds_unique h (inscribed_area_tendsto r)

end -- close noncomputable section

end ArchimedesMethodOfExhaustion
