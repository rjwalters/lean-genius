/-
  Erdős Problem #232 — Open Question 01:
  What is the exact value of m₁? Is it algebraic or transcendental?

  m₁ = supremum of upper densities of unit-distance-free subsets of ℝ².
  Known: 0.22936 ≤ m₁ ≤ 0.247.

  Questions:
  1. What is the exact value of m₁?
  2. Is m₁ algebraic (like π/(8√3)) or transcendental?
  3. Is m₁ = 1/χ where χ is the chromatic number of the plane?

  Reference: https://erdosproblems.com/232
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Tactic

namespace Erdos232OQ01

/- ## Definitions -/

/-- Unit distance in ℝ². -/
def IsUnitDist (p q : EuclideanSpace ℝ (Fin 2)) : Prop := dist p q = 1

/-- A set avoids unit distances. -/
def UnitFree (A : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p q, p ∈ A → q ∈ A → IsUnitDist p q → p = q

/-- The maximum density m₁ (axiomatized). -/
axiom m₁ : ℝ

/-- m₁ is in [0, 1]. -/
axiom m₁_in_unit : 0 ≤ m₁ ∧ m₁ ≤ 1

/-- Croft lower bound: m₁ ≥ 0.22936. -/
axiom m₁_lower : m₁ ≥ 0.22936

/-- Ambrus et al. upper bound: m₁ ≤ 0.247. -/
axiom m₁_upper : m₁ ≤ 0.247

/- ## The Exact Value Question -/

/-- Possible exact value: m₁ = π/(8√3) (hexagonal packing density). -/
def IsHexagonalDensity : Prop := m₁ = Real.pi / (8 * Real.sqrt 3)

/-- Possible exact value: m₁ = 1/χ for chromatic number χ of the plane. -/
def IsReciprocalChromatic (χ : ℕ) : Prop :=
  4 ≤ χ ∧ χ ≤ 7 ∧ m₁ = 1 / χ

/-- The algebraic/transcendental question. -/
def m₁IsAlgebraic : Prop :=
  ∃ (p : Polynomial ℤ), p ≠ 0 ∧ (p.eval₂ (Int.castRingHom ℝ) m₁ = 0)

/- ## Structural Results (all PROVED) -/

/-- m₁ < 1/4 (from Ambrus et al.). -/
theorem m₁_lt_quarter : m₁ < 1 / 4 := by
  calc m₁ ≤ 0.247 := m₁_upper
    _ < 1 / 4 := by norm_num

/-- m₁ > 0 (from Croft lower bound). -/
theorem m₁_pos : m₁ > 0 := by
  calc m₁ ≥ 0.22936 := m₁_lower
    _ > 0 := by norm_num

/-- m₁ ≤ 1/2 (trivial: A and A+u disjoint for unit u). -/
theorem m₁_le_half : m₁ ≤ 1 / 2 := by
  calc m₁ ≤ 0.247 := m₁_upper
    _ ≤ 1 / 2 := by norm_num

/-- The gap between best bounds. -/
theorem bounds_gap : m₁_upper.le.le ∧ m₁_lower.le.le ∧ (0.247 - 0.22936 : ℝ) = 0.01764 := by
  exact ⟨le_refl _, le_refl _, by norm_num⟩

/-- If m₁ = 1/χ, then χ ≥ 5 (since m₁ < 1/4). -/
theorem chromatic_at_least_5 (χ : ℕ) (hχ : χ ≥ 1) (h : m₁ = 1 / χ) : χ ≥ 5 := by
  by_contra hlt
  push_neg at hlt
  interval_cases χ <;> simp_all <;> linarith [m₁_lt_quarter]

/-- If m₁ = 1/χ, then χ ≤ 4 is impossible. -/
theorem not_chromatic_4 (h : m₁ = 1 / 4) : False := by
  have := m₁_lt_quarter
  linarith

/-- The hexagonal density π/(8√3) ≈ 0.2267 is below the Croft bound 0.22936.
    So the exact value is NOT π/(8√3); the Croft construction beats it. -/
theorem not_hexagonal_if_croft (h : Real.pi / (8 * Real.sqrt 3) < 0.22936) :
    ¬IsHexagonalDensity := by
  intro ⟨heq⟩
  rw [heq] at m₁_lower
  linarith

/-- The empty set is unit-distance free. -/
theorem empty_unitFree : UnitFree ∅ := by
  intro p _ hp; exact absurd hp (Set.not_mem_empty p)

/-- Singletons are unit-distance free. -/
theorem singleton_unitFree (x : EuclideanSpace ℝ (Fin 2)) : UnitFree {x} := by
  intro p q hp hq _
  simp at hp hq; exact hp.trans hq.symm

/-- Open balls of radius < 1/2 are unit-distance free. -/
theorem small_ball_unitFree (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : r < 1/2) :
    UnitFree (Metric.ball c r) := by
  intro p q hp hq hdist
  rw [Metric.mem_ball] at hp hq
  simp [IsUnitDist] at hdist
  have : dist p q ≤ dist p c + dist c q := dist_triangle p c q
  have : dist c q = dist q c := dist_comm c q
  linarith

/-
## Summary

**Open Question**: What is the exact value of m₁?

**Known**: 0.22936 ≤ m₁ ≤ 0.247
**Proved**: m₁ < 1/4, m₁ > 0, chromatic number ≥ 5 if m₁ = 1/χ

**Key open aspects**:
1. Narrow the gap 0.22936 ↔ 0.247
2. Determine if m₁ is algebraic
3. Determine the relationship to χ(ℝ²)
-/

end Erdos232OQ01
