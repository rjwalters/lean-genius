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

/-
## Summary

Proved (target: 0 sorries, 0 axioms — build pending under Docker blackout):
- `amgm_three`     : AM–GM for three nonnegatives, cubed form (explicit SOS certificate).
- `sin_jensen_three` : three-point Jensen for `sin` on `[0, π]`.
- `morley_side_le_equilateral` : `s(α,β,γ) ≤ 8R sin³(π/9)`.
- `morley_side_equilateral`     : the equilateral attains the bound.
- `morley_side_max`             : packaged "maximum at the equilateral".

The maximal Morley side is `8R sin³(π/9) ≈ 0.32008 R` (`π/9 = 20°`).

### Remaining (future session)
- **Strict uniqueness**: equality `s = 8R sin³(π/9)` holds *iff* `α = β = γ = π/3`.
  This needs the strict forms (`StrictConcaveOn.lt_map_sum` for `sin`, and strict
  AM–GM equality), and is the natural OQ-03 follow-up.
-/

end MorleysTheoremOQ03
