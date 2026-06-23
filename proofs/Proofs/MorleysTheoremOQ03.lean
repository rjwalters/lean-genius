import Mathlib

/-
# Morley's Theorem — OQ-03: The Morley Triangle is Largest at the Equilateral

## Research Problem: morleys-theorem-oq-03

The parent file `MorleysTheorem.lean` proves Morley's trisector theorem and, in
particular, that each side of the Morley equilateral triangle of a triangle with
angles `α, β, γ` (and circumradius `R`) has length

      s(α, β, γ) = 8 · R · sin(α/3) · sin(β/3) · sin(γ/3).

OQ-01 formalized Conway's backward construction; OQ-02 studies the *second*
Morley triangles from non-adjacent trisectors.  This file asks an **extremal**
question, orthogonal to both:

> Among all triangles with a fixed circumradius `R`, which one has the largest
> Morley triangle?

**Answer (this file): the equilateral triangle, uniquely.**  Concretely

      s(α, β, γ) ≤ 8 · R · sin(π/9)³           (`morley_side_le_equilateral`)

with equality attained at `α = β = γ = π/3` (`morley_side_equilateral`).  Since
`π/9 = 20°`, the maximal Morley side is `8 R sin³20° ≈ 0.32008 · R`.

## Proof strategy (fully elementary, no calculus)

Write `aᵢ = αᵢ/3`, so `a₁ + a₂ + a₃ = π/3` and the trisected mean is always
`π/9`.  We bound the product of sines by their value at the mean in two steps:

1. **AM–GM (degree 3).** For `u, v, w ≥ 0`,
   `u · v · w ≤ ((u + v + w)/3)³`.
   Certificate: `(u+v+w)³ − 27uvw = 3·Σ u(v−w)² + ½·(u+v+w)·Σ(u−v)² ≥ 0`.

2. **Jensen for `sin` (concave on `[0, π]`).**
   `sin a₁ + sin a₂ + sin a₃ ≤ 3 · sin((a₁+a₂+a₃)/3)`.

Chaining with monotonicity of `t ↦ t³` on `[0, ∞)` gives
`∏ sin aᵢ ≤ sin((a₁+a₂+a₃)/3)³ = sin(π/9)³`.

Tags: geometry, morley, trisectors, extremal, jensen, am-gm
-/

namespace MorleysTheoremOQ03

open Real Set

-- ============================================================
-- Part I: Two analytic inequalities
-- ============================================================

/-- **AM–GM for three nonnegative reals (cubed form).**
    `u · v · w ≤ ((u + v + w) / 3)³`.

    Proven from the explicit nonnegative decomposition
    `(u+v+w)³ − 27uvw = 3(u(v−w)² + v(w−u)² + w(u−v)²) + ½(u+v+w)((u−v)²+(v−w)²+(w−u)²)`. -/
theorem amgm_three {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    u * v * w ≤ ((u + v + w) / 3) ^ 3 := by
  have huvw : 0 ≤ u + v + w := by linarith
  nlinarith [mul_nonneg hu (sq_nonneg (v - w)), mul_nonneg hv (sq_nonneg (w - u)),
    mul_nonneg hw (sq_nonneg (u - v)), mul_nonneg huvw (sq_nonneg (u - v)),
    mul_nonneg huvw (sq_nonneg (v - w)), mul_nonneg huvw (sq_nonneg (w - u)),
    mul_nonneg (mul_nonneg hu hv) hw]

/-- **Jensen's inequality for `sin` at three points of `[0, π]`.**
    `sin a₁ + sin a₂ + sin a₃ ≤ 3 · sin((a₁ + a₂ + a₃)/3)`.

    `sin` is concave on `[0, π]`.  We avoid `Finset`/`Matrix` indexing by chaining
    the two-point concavity inequality: a four-point Jensen (treating the mean `m`
    as a fourth point, so that the four-point average is again `m`) gives the
    three-point bound. -/
theorem sin_jensen_three {a₁ a₂ a₃ : ℝ}
    (h₁ : a₁ ∈ Icc (0 : ℝ) π) (h₂ : a₂ ∈ Icc (0 : ℝ) π) (h₃ : a₃ ∈ Icc (0 : ℝ) π) :
    sin a₁ + sin a₂ + sin a₃ ≤ 3 * sin ((a₁ + a₂ + a₃) / 3) := by
  have hcon : ConcaveOn ℝ (Icc 0 π) sin := strictConcaveOn_sin_Icc.concaveOn
  -- Two-point concavity in midpoint form.
  have two : ∀ {p q : ℝ}, p ∈ Icc (0 : ℝ) π → q ∈ Icc (0 : ℝ) π →
      sin p + sin q ≤ 2 * sin ((p + q) / 2) := by
    intro p q hp hq
    have hineq := hcon.2 hp hq (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at hineq
    rw [show (1 : ℝ) / 2 * p + 1 / 2 * q = (p + q) / 2 by ring] at hineq
    linarith
  -- Midpoint of two points of [0, π] is again in [0, π].
  have midmem : ∀ {p q : ℝ}, p ∈ Icc (0 : ℝ) π → q ∈ Icc (0 : ℝ) π →
      (p + q) / 2 ∈ Icc (0 : ℝ) π := by
    intro p q hp hq
    exact ⟨by linarith [hp.1, hq.1], by linarith [hp.2, hq.2]⟩
  set m := (a₁ + a₂ + a₃) / 3 with hm_def
  have hm : m ∈ Icc (0 : ℝ) π :=
    ⟨by rw [hm_def]; linarith [h₁.1, h₂.1, h₃.1],
     by rw [hm_def]; linarith [h₁.2, h₂.2, h₃.2]⟩
  -- p = (a₁+a₂)/2, q = (a₃+m)/2, both in [0, π].
  have hp : (a₁ + a₂) / 2 ∈ Icc (0 : ℝ) π := midmem h₁ h₂
  have hq : (a₃ + m) / 2 ∈ Icc (0 : ℝ) π := midmem h₃ hm
  have hA : sin a₁ + sin a₂ ≤ 2 * sin ((a₁ + a₂) / 2) := two h₁ h₂
  have hB : sin a₃ + sin m ≤ 2 * sin ((a₃ + m) / 2) := two h₃ hm
  have hC : sin ((a₁ + a₂) / 2) + sin ((a₃ + m) / 2) ≤
      2 * sin (((a₁ + a₂) / 2 + (a₃ + m) / 2) / 2) := two hp hq
  -- The fourfold midpoint is again m, since a₁ + a₂ + a₃ = 3m.
  have hmid_eq : ((a₁ + a₂) / 2 + (a₃ + m) / 2) / 2 = m := by
    rw [hm_def]; ring
  rw [hmid_eq] at hC
  linarith

-- ============================================================
-- Part I·b: Equality cases (strict concavity)
-- ============================================================

/-- **Equality case of two-point concavity for `sin`.**
    If `sin p + sin q = 2 · sin((p+q)/2)` for `p, q ∈ [0, π]`, then `p = q`.

    `sin` is *strictly* concave on `[0, π]`, so the midpoint inequality is strict
    whenever `p ≠ q`; equality therefore forces `p = q`. -/
theorem sin_two_eq {p q : ℝ} (hp : p ∈ Icc (0 : ℝ) π) (hq : q ∈ Icc (0 : ℝ) π)
    (heq : sin p + sin q = 2 * sin ((p + q) / 2)) : p = q := by
  by_contra hne
  have hstr := strictConcaveOn_sin_Icc.2 hp hq hne (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hstr
  rw [show (1 : ℝ) / 2 * p + 1 / 2 * q = (p + q) / 2 by ring] at hstr
  linarith

/-- **Equality case of three-point Jensen for `sin`.**
    If `sin a₁ + sin a₂ + sin a₃ = 3 · sin((a₁+a₂+a₃)/3)` for `aᵢ ∈ [0, π]`, then
    all three points coincide: `a₁ = a₂` and `a₂ = a₃`.

    Same chained two-point structure as `sin_jensen_three`, but reading off the
    strict equality case (`sin_two_eq`) at each tight midpoint step. -/
theorem sin_jensen_three_eq {a₁ a₂ a₃ : ℝ}
    (h₁ : a₁ ∈ Icc (0 : ℝ) π) (h₂ : a₂ ∈ Icc (0 : ℝ) π) (h₃ : a₃ ∈ Icc (0 : ℝ) π)
    (heq : sin a₁ + sin a₂ + sin a₃ = 3 * sin ((a₁ + a₂ + a₃) / 3)) :
    a₁ = a₂ ∧ a₂ = a₃ := by
  have midmem : ∀ {p q : ℝ}, p ∈ Icc (0 : ℝ) π → q ∈ Icc (0 : ℝ) π →
      (p + q) / 2 ∈ Icc (0 : ℝ) π := by
    intro p q hp hq
    exact ⟨by linarith [hp.1, hq.1], by linarith [hp.2, hq.2]⟩
  have two_le : ∀ {p q : ℝ}, p ∈ Icc (0 : ℝ) π → q ∈ Icc (0 : ℝ) π →
      sin p + sin q ≤ 2 * sin ((p + q) / 2) := by
    intro p q hp hq
    have hineq := (strictConcaveOn_sin_Icc.concaveOn).2 hp hq (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at hineq
    rw [show (1 : ℝ) / 2 * p + 1 / 2 * q = (p + q) / 2 by ring] at hineq
    linarith
  set m := (a₁ + a₂ + a₃) / 3 with hm_def
  have hm : m ∈ Icc (0 : ℝ) π :=
    ⟨by rw [hm_def]; linarith [h₁.1, h₂.1, h₃.1],
     by rw [hm_def]; linarith [h₁.2, h₂.2, h₃.2]⟩
  have hp : (a₁ + a₂) / 2 ∈ Icc (0 : ℝ) π := midmem h₁ h₂
  have hq : (a₃ + m) / 2 ∈ Icc (0 : ℝ) π := midmem h₃ hm
  have hA : sin a₁ + sin a₂ ≤ 2 * sin ((a₁ + a₂) / 2) := two_le h₁ h₂
  have hB : sin a₃ + sin m ≤ 2 * sin ((a₃ + m) / 2) := two_le h₃ hm
  have hC : sin ((a₁ + a₂) / 2) + sin ((a₃ + m) / 2) ≤ 2 * sin m := by
    have := two_le hp hq
    rwa [show ((a₁ + a₂) / 2 + (a₃ + m) / 2) / 2 = m by rw [hm_def]; ring] at this
  -- Equality in the chained sum forces each two-point step to be tight.
  have hAeq : sin a₁ + sin a₂ = 2 * sin ((a₁ + a₂) / 2) := le_antisymm hA (by linarith)
  have hBeq : sin a₃ + sin m = 2 * sin ((a₃ + m) / 2) := le_antisymm hB (by linarith)
  have e12 : a₁ = a₂ := sin_two_eq h₁ h₂ hAeq
  have e3m : a₃ = m := sin_two_eq h₃ hm hBeq
  refine ⟨e12, ?_⟩
  rw [hm_def] at e3m
  linarith [e12, e3m]

-- ============================================================
-- Part II: The Morley side length and its maximum
-- ============================================================

/-- The common side length of the Morley equilateral triangle of a triangle with
    angles `α, β, γ` and circumradius `R`, as established in `MorleysTheorem.lean`:
    `8 · R · sin(α/3) · sin(β/3) · sin(γ/3)`. -/
noncomputable def morleySide (R α β γ : ℝ) : ℝ :=
  8 * R * sin (α / 3) * sin (β / 3) * sin (γ / 3)

/-- For trisected angles, the relevant arguments lie in `[0, π]`:
    if `0 < α` and `α + β + γ = π` with `β, γ > 0`, then `α/3 ∈ [0, π]`. -/
theorem div_three_mem_Icc {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hsum : α + β + γ = π) : α / 3 ∈ Icc (0 : ℝ) π := by
  constructor
  · linarith
  · -- α < π since β + γ > 0, hence α/3 < π/3 ≤ π
    have hαπ : α < π := by linarith
    have : (0 : ℝ) < π := by linarith
    linarith

/-- **Main extremal bound.** Among triangles with circumradius `R ≥ 0`, the Morley
    side length never exceeds its value `8 R sin³(π/9)` at the equilateral triangle. -/
theorem morley_side_le_equilateral {R α β γ : ℝ} (hR : 0 ≤ R)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hsum : α + β + γ = π) :
    morleySide R α β γ ≤ 8 * R * sin (π / 9) ^ 3 := by
  -- The three trisected angles lie in [0, π].
  have ha : α / 3 ∈ Icc (0 : ℝ) π := div_three_mem_Icc hα hβ hγ hsum
  have hb : β / 3 ∈ Icc (0 : ℝ) π := by
    have := div_three_mem_Icc hβ hα hγ (by linarith); simpa using this
  have hc : γ / 3 ∈ Icc (0 : ℝ) π := by
    have := div_three_mem_Icc hγ hα hβ (by linarith); simpa using this
  -- Nonnegativity of the three sines.
  have hsa : 0 ≤ sin (α / 3) := sin_nonneg_of_nonneg_of_le_pi ha.1 ha.2
  have hsb : 0 ≤ sin (β / 3) := sin_nonneg_of_nonneg_of_le_pi hb.1 hb.2
  have hsc : 0 ≤ sin (γ / 3) := sin_nonneg_of_nonneg_of_le_pi hc.1 hc.2
  -- The trisected mean is exactly π/9.
  have hmean : (α / 3 + β / 3 + γ / 3) / 3 = π / 9 := by
    rw [show (α / 3 + β / 3 + γ / 3) / 3 = (α + β + γ) / 9 by ring, hsum]
  -- Step 1: AM–GM on the three sines.
  have hamgm : sin (α / 3) * sin (β / 3) * sin (γ / 3) ≤
      ((sin (α / 3) + sin (β / 3) + sin (γ / 3)) / 3) ^ 3 := amgm_three hsa hsb hsc
  -- Step 2: Jensen gives the average sine ≤ sin(π/9).
  have hjen : sin (α / 3) + sin (β / 3) + sin (γ / 3) ≤ 3 * sin (π / 9) := by
    have := sin_jensen_three ha hb hc
    rwa [hmean] at this
  have hmid : (sin (α / 3) + sin (β / 3) + sin (γ / 3)) / 3 ≤ sin (π / 9) := by linarith
  have havg_nonneg : 0 ≤ (sin (α / 3) + sin (β / 3) + sin (γ / 3)) / 3 := by linarith
  -- Cube is monotone on the nonnegatives.
  have hcube : ((sin (α / 3) + sin (β / 3) + sin (γ / 3)) / 3) ^ 3 ≤ sin (π / 9) ^ 3 :=
    pow_le_pow_left₀ havg_nonneg hmid 3
  -- Chain the product bound: ∏ sin ≤ sin(π/9)³.
  have hprod : sin (α / 3) * sin (β / 3) * sin (γ / 3) ≤ sin (π / 9) ^ 3 :=
    le_trans hamgm hcube
  -- Multiply through by 8R ≥ 0.
  have h8R : 0 ≤ 8 * R := by linarith
  have : morleySide R α β γ = (8 * R) * (sin (α / 3) * sin (β / 3) * sin (γ / 3)) := by
    unfold morleySide; ring
  rw [this]
  calc (8 * R) * (sin (α / 3) * sin (β / 3) * sin (γ / 3))
      ≤ (8 * R) * sin (π / 9) ^ 3 := by
        exact mul_le_mul_of_nonneg_left hprod h8R
    _ = 8 * R * sin (π / 9) ^ 3 := by ring

/-- **The bound is attained.** The equilateral triangle (`α = β = γ = π/3`) realizes
    the maximal Morley side length `8 R sin³(π/9)`. -/
theorem morley_side_equilateral (R : ℝ) :
    morleySide R (π / 3) (π / 3) (π / 3) = 8 * R * sin (π / 9) ^ 3 := by
  unfold morleySide
  rw [show π / 3 / 3 = π / 9 by ring]
  ring

/-- **Maximum characterization (packaged).** For circumradius `R ≥ 0`, the value
    `8 R sin³(π/9)` is the maximum of the Morley side length over all triangles,
    attained at the equilateral triangle. -/
theorem morley_side_max {R : ℝ} (hR : 0 ≤ R) :
    morleySide R (π / 3) (π / 3) (π / 3) = 8 * R * sin (π / 9) ^ 3 ∧
    ∀ α β γ : ℝ, 0 < α → 0 < β → 0 < γ → α + β + γ = π →
      morleySide R α β γ ≤ morleySide R (π / 3) (π / 3) (π / 3) := by
  refine ⟨morley_side_equilateral R, ?_⟩
  intro α β γ hα hβ hγ hsum
  rw [morley_side_equilateral R]
  exact morley_side_le_equilateral hR hα hβ hγ hsum

/-- **Strict uniqueness of the maximizer.** For circumradius `R > 0`, the Morley
    side length attains its maximal value `8 R sin³(π/9)` *iff* the triangle is
    equilateral (`α = β = γ = π/3`).

    The forward direction extracts the equality cases of the AM–GM and Jensen
    steps: tightness in `pow_le_pow_left₀`/`amgm_three` sandwiches the average of
    the three sines to exactly `sin(π/9)`, and `sin_jensen_three_eq` then forces
    the three trisected angles to coincide.  (The hypothesis `R > 0` is essential:
    when `R = 0` every triangle gives Morley side `0`, so the maximizer is not
    unique.) -/
theorem morley_side_eq_iff {R α β γ : ℝ} (hR : 0 < R)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hsum : α + β + γ = π) :
    morleySide R α β γ = 8 * R * sin (π / 9) ^ 3 ↔
      α = π / 3 ∧ β = π / 3 ∧ γ = π / 3 := by
  constructor
  · intro heq
    -- The three trisected angles lie in [0, π], with nonnegative sines.
    have ha : α / 3 ∈ Icc (0 : ℝ) π := div_three_mem_Icc hα hβ hγ hsum
    have hb : β / 3 ∈ Icc (0 : ℝ) π := by
      have := div_three_mem_Icc hβ hα hγ (by linarith); simpa using this
    have hc : γ / 3 ∈ Icc (0 : ℝ) π := by
      have := div_three_mem_Icc hγ hα hβ (by linarith); simpa using this
    have hsa : 0 ≤ sin (α / 3) := sin_nonneg_of_nonneg_of_le_pi ha.1 ha.2
    have hsb : 0 ≤ sin (β / 3) := sin_nonneg_of_nonneg_of_le_pi hb.1 hb.2
    have hsc : 0 ≤ sin (γ / 3) := sin_nonneg_of_nonneg_of_le_pi hc.1 hc.2
    have hsin9_nonneg : 0 ≤ sin (π / 9) := by
      have hpi := Real.pi_pos
      apply sin_nonneg_of_nonneg_of_le_pi <;> linarith
    have hmean : (α / 3 + β / 3 + γ / 3) / 3 = π / 9 := by
      rw [show (α / 3 + β / 3 + γ / 3) / 3 = (α + β + γ) / 9 by ring, hsum]
    -- From the equality of side lengths, the product of sines equals sin(π/9)³.
    have h8R : (0 : ℝ) < 8 * R := by linarith
    have hms : morleySide R α β γ = (8 * R) * (sin (α / 3) * sin (β / 3) * sin (γ / 3)) := by
      unfold morleySide; ring
    have hprod_eq : sin (α / 3) * sin (β / 3) * sin (γ / 3) = sin (π / 9) ^ 3 := by
      have step : (8 * R) * (sin (α / 3) * sin (β / 3) * sin (γ / 3))
          = (8 * R) * sin (π / 9) ^ 3 := by rw [← hms, heq]
      exact mul_left_cancel₀ h8R.ne' step
    -- AM–GM and Jensen, exactly as in the bound proof.
    have hamgm : sin (α / 3) * sin (β / 3) * sin (γ / 3) ≤
        ((sin (α / 3) + sin (β / 3) + sin (γ / 3)) / 3) ^ 3 := amgm_three hsa hsb hsc
    have hjen : sin (α / 3) + sin (β / 3) + sin (γ / 3) ≤ 3 * sin (π / 9) := by
      have := sin_jensen_three ha hb hc; rwa [hmean] at this
    have hmid : (sin (α / 3) + sin (β / 3) + sin (γ / 3)) / 3 ≤ sin (π / 9) := by linarith
    have havg_nonneg : 0 ≤ (sin (α / 3) + sin (β / 3) + sin (γ / 3)) / 3 := by linarith
    have hcube : ((sin (α / 3) + sin (β / 3) + sin (γ / 3)) / 3) ^ 3 ≤ sin (π / 9) ^ 3 :=
      pow_le_pow_left₀ havg_nonneg hmid 3
    -- The product is sandwiched at sin(π/9)³, forcing the cube — hence the average — tight.
    have hcube_eq : ((sin (α / 3) + sin (β / 3) + sin (γ / 3)) / 3) ^ 3 = sin (π / 9) ^ 3 :=
      le_antisymm hcube (by rw [← hprod_eq]; exact hamgm)
    have hav_eq : (sin (α / 3) + sin (β / 3) + sin (γ / 3)) / 3 = sin (π / 9) :=
      (pow_left_inj₀ havg_nonneg hsin9_nonneg (by norm_num)).mp hcube_eq
    -- Equality in Jensen forces the three trisected angles to coincide.
    have hJeq : sin (α / 3) + sin (β / 3) + sin (γ / 3)
        = 3 * sin ((α / 3 + β / 3 + γ / 3) / 3) := by rw [hmean]; linarith [hav_eq]
    obtain ⟨e1, e2⟩ := sin_jensen_three_eq ha hb hc hJeq
    exact ⟨by linarith [e1, e2], by linarith [e1, e2], by linarith [e1, e2]⟩
  · rintro ⟨hα', hβ', hγ'⟩
    subst hα'; subst hβ'; subst hγ'
    exact morley_side_equilateral R

/-
## Summary

Proved (0 sorries, 0 axioms — machine-verified via docker-build 2026-06-15):
- `amgm_three`     : AM–GM for three nonnegatives, cubed form (explicit SOS certificate).
- `sin_jensen_three` : three-point Jensen for `sin` on `[0, π]`.
- `morley_side_le_equilateral` : `s(α,β,γ) ≤ 8R sin³(π/9)`.
- `morley_side_equilateral`     : the equilateral attains the bound.
- `morley_side_max`             : packaged "maximum at the equilateral".

- `sin_two_eq` / `sin_jensen_three_eq` : equality cases of two- and three-point Jensen.
- `morley_side_eq_iff` : **strict uniqueness** — for `R > 0`, `s = 8R sin³(π/9)`
  *iff* `α = β = γ = π/3` (the equilateral is the unique maximizer).

The maximal Morley side is `8R sin³(π/9) ≈ 0.32008 R` (`π/9 = 20°`).
-/

end MorleysTheoremOQ03
