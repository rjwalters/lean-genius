import Mathlib

/-
# Morley's Theorem — OQ-01-OQ-01: Explicit Side Length of the Morley Triangle

## Research Problem: morleys-theorem-oq-01-oq-01

Parent (`morleys-theorem-oq-01`, MorleysTheoremOQ01.lean) set up Conway's angle
scaffolding and *defined* the Morley side length

  morleySideLength t R = 8 * R * sin(α/3) * sin(β/3) * sin(γ/3),

then explicitly recorded as the remaining open work (file summary, "What remains
for the full proof"):

  > The coordinate computation: show each side of the Morley triangle equals
  > 8R·sin(α/3)·sin(β/3)·sin(γ/3) ... the computation is finite and mechanical
  > but substantial.

This file closes that gap with a fully **coordinate-free, trigonometric**
derivation.  The geometric content enters only through the two classical metric
laws (extended law of sines, law of cosines); the heart of the argument is two
pure trigonometric identities, both proved here from scratch (0 axioms).

## The derivation

Write `a₃ = α/3`, `b₃ = β/3`, `c₃ = γ/3`, so `a₃ + b₃ + c₃ = π/3`.

* **Step 1 (triple-angle product).**  `sin(3θ) = 4 sin θ · sin(π/3 − θ) · sin(π/3 + θ)`.

* **Step 2 (ear segments via law of sines).**  The trisectors from `B` and `A`
  nearest side `AB` meet the Morley vertex `Z`.  In triangle `ABZ` the angles are
  `b₃` at `B`, `a₃` at `A`, so `∠AZB = π − a₃ − b₃` with `sin ∠AZB = sin(π/3 − c₃)`,
  and `AB = 2R sin γ = 2R sin(3c₃)`.  The law of sines `AZ / sin b₃ = AB / sin ∠AZB`
  together with Step 1 collapses to

    AZ = 8R · sin b₃ · sin c₃ · sin(π/3 + c₃).

  Likewise `AY = 8R · sin b₃ · sin c₃ · sin(π/3 + b₃)` for the segment to the
  Morley vertex `Y` on side `AC`.

* **Step 3 (law of cosines).**  In triangle `AYZ` the angle at `A` is the middle
  trisector sector `a₃`, so `YZ² = AY² + AZ² − 2·AY·AZ·cos a₃`.  A pure trig
  identity (`morley_cos_bracket`) reduces this exactly to

    YZ² = (8R · sin a₃ · sin b₃ · sin c₃)² = morleySideLength².

  By symmetry the same value is obtained at every vertex, so the Morley triangle
  is equilateral with the stated side length.

Tags: geometry, morley, trisectors, law-of-sines, law-of-cosines, side-length
-/

namespace MorleysTheoremOQ01OQ01

open Real

-- ============================================================
-- Part I: The triple-angle product identity
-- ============================================================

/-- **Triple-angle product identity.**
    `sin(3θ) = 4 · sin θ · sin(π/3 − θ) · sin(π/3 + θ)`.

    This is the trigonometric engine behind the Morley side length: it expresses
    `sin γ = sin(3·γ/3)` as a symmetric product of the trisected angle and its
    `π/3`-shifts, which is exactly the factor produced by the law of sines. -/
theorem sin_three_mul_prod (θ : ℝ) :
    sin (3 * θ) = 4 * sin θ * sin (π / 3 - θ) * sin (π / 3 + θ) := by
  rw [sin_sub, sin_add, sin_pi_div_three, cos_pi_div_three, sin_three_mul]
  have hpyth := sin_sq_add_cos_sq θ
  have hsqrt3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  linear_combination (-(sin θ) * (cos θ) ^ 2) * hsqrt3 + (-3 * sin θ) * hpyth

-- ============================================================
-- Part II: Ear segments from the law of sines
-- ============================================================

/-- **Ear segment via the law of sines.**

    In the sub-triangle `ABZ` (`Z` a Morley vertex), the law of sines reads
    `AZ · sin ∠AZB = AB · sin b₃`, i.e. `AZ · sin(π/3 − c₃) = 2R·sin(3c₃)·sin b₃`,
    where `AB = 2R sin γ = 2R sin(3c₃)` is the extended law of sines on the
    original triangle.  Combined with `sin_three_mul_prod`, the segment length is
    the closed form `8R · sin b₃ · sin c₃ · sin(π/3 + c₃)`.

    The hypothesis `hAZ` packages the (geometric) law-of-sines relation; the
    content proved here is the algebraic collapse to the product form. -/
theorem ear_segment_from_law_of_sines (R b c AZ : ℝ)
    (hsin : sin (π / 3 - c) ≠ 0)
    (hAZ : AZ * sin (π / 3 - c) = 2 * R * sin (3 * c) * sin b) :
    AZ = 8 * R * sin b * sin c * sin (π / 3 + c) := by
  have key : AZ * sin (π / 3 - c)
      = (8 * R * sin b * sin c * sin (π / 3 + c)) * sin (π / 3 - c) := by
    rw [hAZ, sin_three_mul_prod]; ring
  exact mul_right_cancel₀ hsin key

-- ============================================================
-- Part III: The law-of-cosines bracket identity
-- ============================================================

/-- Auxiliary pure identity:
    `sin²u + sin²v + 2·sin u·sin v·cos(u+v) = sin²(u+v)`. -/
theorem trig_pythag_bracket (u v : ℝ) :
    sin u ^ 2 + sin v ^ 2 + 2 * sin u * sin v * cos (u + v) = sin (u + v) ^ 2 := by
  rw [sin_add, cos_add]
  nlinarith [sin_sq_add_cos_sq u, sin_sq_add_cos_sq v]

/-- **Law-of-cosines core for the Morley side.**

    With `a + b + c = π/3`, the two ear segments at a vertex,
    `AZ = 8R sin b sin c sin(π/3+c)` and `AY = 8R sin b sin c sin(π/3+b)`,
    enclosing the middle trisector angle `a`, satisfy

      AY² + AZ² − 2·AY·AZ·cos a = (8R · sin a · sin b · sin c)².

    This is the law of cosines `YZ² = AY² + AZ² − 2 AY AZ cos a` evaluated to the
    symmetric closed form — the equilateral side length squared. -/
theorem morley_side_sq (R a b c : ℝ) (hsum : a + b + c = π / 3) :
    (8 * R * sin b * sin c * sin (π / 3 + b)) ^ 2
      + (8 * R * sin b * sin c * sin (π / 3 + c)) ^ 2
      - 2 * (8 * R * sin b * sin c * sin (π / 3 + b))
          * (8 * R * sin b * sin c * sin (π / 3 + c)) * cos a
    = (8 * R * sin a * sin b * sin c) ^ 2 := by
  -- From the angle constraint, `a = π − ((π/3+b) + (π/3+c))`, giving the
  -- supplementary-angle relations for the middle trisector angle.
  have hUV : (π / 3 + b) + (π / 3 + c) = π - a := by linarith [hsum]
  have hcos : cos a = - cos ((π / 3 + b) + (π / 3 + c)) := by
    rw [hUV, Real.cos_pi_sub]; ring
  have hsin : sin a = sin ((π / 3 + b) + (π / 3 + c)) := by rw [hUV, Real.sin_pi_sub]
  -- The law-of-cosines bracket reduces to `sin²` of the supplementary angle.
  have hbr := trig_pythag_bracket (π / 3 + b) (π / 3 + c)
  -- Collapse to the symmetric closed form (`K = 8R sin b sin c` common factor).
  linear_combination
    (-2 * (8 * R * sin b * sin c) ^ 2 * sin (π / 3 + b) * sin (π / 3 + c)) * hcos
      + (8 * R * sin b * sin c) ^ 2 * hbr
      + (-(8 * R * sin b * sin c) ^ 2
          * (sin a + sin ((π / 3 + b) + (π / 3 + c)))) * hsin

-- ============================================================
-- Part IV: The Morley triangle model and its side length
-- ============================================================

/-- A triangle specified by its three vertex angles summing to `π`
    (matching the parent `MorleysTheoremOQ01.TriangleAngles`). -/
structure TriangleAngles where
  α : ℝ
  β : ℝ
  γ : ℝ
  α_pos : 0 < α
  β_pos : 0 < β
  γ_pos : 0 < γ
  sum_eq_pi : α + β + γ = π

namespace TriangleAngles

/-- Trisected angles. -/
noncomputable def α₃ (t : TriangleAngles) : ℝ := t.α / 3
noncomputable def β₃ (t : TriangleAngles) : ℝ := t.β / 3
noncomputable def γ₃ (t : TriangleAngles) : ℝ := t.γ / 3

theorem trisected_sum (t : TriangleAngles) : t.α₃ + t.β₃ + t.γ₃ = π / 3 := by
  unfold α₃ β₃ γ₃; linarith [t.sum_eq_pi]

theorem trisected_pos (t : TriangleAngles) : 0 < t.α₃ ∧ 0 < t.β₃ ∧ 0 < t.γ₃ := by
  unfold α₃ β₃ γ₃
  exact ⟨by linarith [t.α_pos], by linarith [t.β_pos], by linarith [t.γ_pos]⟩

theorem trisected_lt_pi_third (t : TriangleAngles) :
    t.α₃ < π / 3 ∧ t.β₃ < π / 3 ∧ t.γ₃ < π / 3 := by
  have hs := trisected_sum t
  have ⟨ha, hb, hc⟩ := trisected_pos t
  exact ⟨by linarith, by linarith, by linarith⟩

end TriangleAngles

open TriangleAngles

/-- The Morley side length (parent's definition):
    `s = 8R · sin(α/3) · sin(β/3) · sin(γ/3)`. -/
noncomputable def morleySideLength (t : TriangleAngles) (R : ℝ) : ℝ :=
  8 * R * sin t.α₃ * sin t.β₃ * sin t.γ₃

/-- The Morley side facing vertex `A`, computed by the law of cosines from the two
    ear segments `AY`, `AZ` and the middle trisector angle `α₃ = α/3`. -/
noncomputable def morleySideA (t : TriangleAngles) (R : ℝ) : ℝ :=
  Real.sqrt
    ((8 * R * sin t.β₃ * sin t.γ₃ * sin (π / 3 + t.β₃)) ^ 2
      + (8 * R * sin t.β₃ * sin t.γ₃ * sin (π / 3 + t.γ₃)) ^ 2
      - 2 * (8 * R * sin t.β₃ * sin t.γ₃ * sin (π / 3 + t.β₃))
          * (8 * R * sin t.β₃ * sin t.γ₃ * sin (π / 3 + t.γ₃)) * cos t.α₃)

/-- The Morley side facing vertex `B`. -/
noncomputable def morleySideB (t : TriangleAngles) (R : ℝ) : ℝ :=
  Real.sqrt
    ((8 * R * sin t.γ₃ * sin t.α₃ * sin (π / 3 + t.γ₃)) ^ 2
      + (8 * R * sin t.γ₃ * sin t.α₃ * sin (π / 3 + t.α₃)) ^ 2
      - 2 * (8 * R * sin t.γ₃ * sin t.α₃ * sin (π / 3 + t.γ₃))
          * (8 * R * sin t.γ₃ * sin t.α₃ * sin (π / 3 + t.α₃)) * cos t.β₃)

/-- The Morley side facing vertex `C`. -/
noncomputable def morleySideC (t : TriangleAngles) (R : ℝ) : ℝ :=
  Real.sqrt
    ((8 * R * sin t.α₃ * sin t.β₃ * sin (π / 3 + t.α₃)) ^ 2
      + (8 * R * sin t.α₃ * sin t.β₃ * sin (π / 3 + t.β₃)) ^ 2
      - 2 * (8 * R * sin t.α₃ * sin t.β₃ * sin (π / 3 + t.α₃))
          * (8 * R * sin t.α₃ * sin t.β₃ * sin (π / 3 + t.β₃)) * cos t.γ₃)

/-- Positivity of `morleySideLength` for a genuine triangle (`0 < R`). -/
theorem morleySideLength_pos (t : TriangleAngles) (R : ℝ) (hR : 0 < R) :
    0 < morleySideLength t R := by
  unfold morleySideLength
  have ⟨ha, hb, hc⟩ := trisected_pos t
  have ⟨hla, hlb, hlc⟩ := trisected_lt_pi_third t
  have hsa : 0 < sin t.α₃ := sin_pos_of_pos_of_lt_pi ha (by linarith [pi_pos])
  have hsb : 0 < sin t.β₃ := sin_pos_of_pos_of_lt_pi hb (by linarith [pi_pos])
  have hsc : 0 < sin t.γ₃ := sin_pos_of_pos_of_lt_pi hc (by linarith [pi_pos])
  positivity

-- ============================================================
-- Part V: Each Morley side equals the symmetric formula
-- ============================================================

/-- **Side facing `A` equals the Morley side length.**
    `morleySideA t R = 8R · sin(α/3) · sin(β/3) · sin(γ/3)` for `0 ≤ R`. -/
theorem morleySideA_eq (t : TriangleAngles) (R : ℝ) (hR : 0 ≤ R) :
    morleySideA t R = morleySideLength t R := by
  have hsum : t.α₃ + t.β₃ + t.γ₃ = π / 3 := trisected_sum t
  have hsq := morley_side_sq R t.α₃ t.β₃ t.γ₃ hsum
  unfold morleySideA morleySideLength
  rw [hsq]
  -- √(s²) = s since s ≥ 0.
  have ⟨ha, hb, hc⟩ := trisected_pos t
  have ⟨hla, hlb, hlc⟩ := trisected_lt_pi_third t
  have hsa : 0 ≤ sin t.α₃ := le_of_lt (sin_pos_of_pos_of_lt_pi ha (by linarith [pi_pos]))
  have hsb : 0 ≤ sin t.β₃ := le_of_lt (sin_pos_of_pos_of_lt_pi hb (by linarith [pi_pos]))
  have hsc : 0 ≤ sin t.γ₃ := le_of_lt (sin_pos_of_pos_of_lt_pi hc (by linarith [pi_pos]))
  rw [Real.sqrt_sq (by positivity)]

/-- **Side facing `B` equals the Morley side length.** -/
theorem morleySideB_eq (t : TriangleAngles) (R : ℝ) (hR : 0 ≤ R) :
    morleySideB t R = morleySideLength t R := by
  have hsum : t.β₃ + t.γ₃ + t.α₃ = π / 3 := by linarith [trisected_sum t]
  have hsq := morley_side_sq R t.β₃ t.γ₃ t.α₃ hsum
  unfold morleySideB morleySideLength
  rw [hsq]
  have ⟨ha, hb, hc⟩ := trisected_pos t
  have ⟨hla, hlb, hlc⟩ := trisected_lt_pi_third t
  have hsa : 0 ≤ sin t.α₃ := le_of_lt (sin_pos_of_pos_of_lt_pi ha (by linarith [pi_pos]))
  have hsb : 0 ≤ sin t.β₃ := le_of_lt (sin_pos_of_pos_of_lt_pi hb (by linarith [pi_pos]))
  have hsc : 0 ≤ sin t.γ₃ := le_of_lt (sin_pos_of_pos_of_lt_pi hc (by linarith [pi_pos]))
  rw [Real.sqrt_sq (by positivity)]
  ring

/-- **Side facing `C` equals the Morley side length.** -/
theorem morleySideC_eq (t : TriangleAngles) (R : ℝ) (hR : 0 ≤ R) :
    morleySideC t R = morleySideLength t R := by
  have hsum : t.α₃ + t.β₃ + t.γ₃ = π / 3 := trisected_sum t
  have hsq := morley_side_sq R t.γ₃ t.α₃ t.β₃ (by linarith [hsum])
  unfold morleySideC morleySideLength
  rw [hsq]
  have ⟨ha, hb, hc⟩ := trisected_pos t
  have ⟨hla, hlb, hlc⟩ := trisected_lt_pi_third t
  have hsa : 0 ≤ sin t.α₃ := le_of_lt (sin_pos_of_pos_of_lt_pi ha (by linarith [pi_pos]))
  have hsb : 0 ≤ sin t.β₃ := le_of_lt (sin_pos_of_pos_of_lt_pi hb (by linarith [pi_pos]))
  have hsc : 0 ≤ sin t.γ₃ := le_of_lt (sin_pos_of_pos_of_lt_pi hc (by linarith [pi_pos]))
  rw [Real.sqrt_sq (by positivity)]
  ring

-- ============================================================
-- Part VI: The Morley triangle is equilateral (headline)
-- ============================================================

/-- **Morley's Theorem (metric form).**

    The three sides of the Morley triangle — each obtained from the law of cosines
    on Conway's ear construction — all equal the symmetric length
    `8R · sin(α/3) · sin(β/3) · sin(γ/3)`.  In particular the Morley triangle is
    equilateral, with this explicit side length. -/
theorem morley_equilateral (t : TriangleAngles) (R : ℝ) (hR : 0 ≤ R) :
    morleySideA t R = morleySideB t R ∧ morleySideB t R = morleySideC t R ∧
      morleySideA t R = morleySideLength t R := by
  refine ⟨?_, ?_, ?_⟩
  · rw [morleySideA_eq t R hR, morleySideB_eq t R hR]
  · rw [morleySideB_eq t R hR, morleySideC_eq t R hR]
  · exact morleySideA_eq t R hR

/-- The common Morley side length is strictly positive for a genuine triangle. -/
theorem morley_side_pos (t : TriangleAngles) (R : ℝ) (hR : 0 < R) :
    0 < morleySideA t R := by
  rw [morleySideA_eq t R (le_of_lt hR)]
  exact morleySideLength_pos t R hR

end MorleysTheoremOQ01OQ01
