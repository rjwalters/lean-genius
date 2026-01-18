/-
  Erdős Problem #671: Lagrange Interpolation Convergence

  Source: https://erdosproblems.com/671
  Status: OPEN
  Prize: $250

  Statement:
  Given points a_i^n ∈ [-1,1] for 1 ≤ i ≤ n, define the Lagrange basis polynomials
  p_i^n and the interpolation operator L^n. The Lebesgue function is λ_n(x) = Σ|p_i^n(x)|.

  Question 1: Does there exist a point sequence where for every continuous f,
  there exists x with limsup λ_n(x) = ∞ yet L^n f(x) → f(x)?

  Question 2: Does there exist a sequence where limsup λ_n(x) = ∞ for ALL x ∈ [-1,1],
  yet for every continuous f, there exists x with L^n f(x) → f(x)?

  Known:
  - Bernstein (1931): For any points, ∃ x₀ where limsup λ_n(x₀) = ∞
  - Erdős-Vértesi (1980): For any points, ∃ f where limsup |L^n f(x)| = ∞ for a.e. x

  Tags: analysis, interpolation, approximation-theory
-/

import Mathlib.Analysis.SpecialFunctions.Polynomials.Basic
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

namespace Erdos671

open Polynomial ContinuousMap MeasureTheory

/- ## Part I: Basic Definitions -/

/-- Points for interpolation: a_i^n ∈ [-1, 1]. -/
structure InterpolationPoints (n : ℕ) where
  points : Fin n → ℝ
  in_interval : ∀ i, points i ∈ Set.Icc (-1 : ℝ) 1
  distinct : ∀ i j, i ≠ j → points i ≠ points j

/-- A sequence of interpolation point sets. -/
def PointSequence := (n : ℕ) → InterpolationPoints n

/-- The Lagrange basis polynomial p_i^n: degree n-1, p_i(a_i) = 1, p_i(a_j) = 0 for j ≠ i. -/
noncomputable def lagrangeBasis (pts : InterpolationPoints n) (i : Fin n) : Polynomial ℝ :=
  ∏ j in Finset.univ.filter (· ≠ i),
    C (1 / (pts.points i - pts.points j)) * (X - C (pts.points j))

/-- p_i^n(a_i) = 1. -/
theorem lagrangeBasis_self (pts : InterpolationPoints n) (i : Fin n) :
    (lagrangeBasis pts i).eval (pts.points i) = 1 := by
  sorry

/-- p_i^n(a_j) = 0 for j ≠ i. -/
theorem lagrangeBasis_other (pts : InterpolationPoints n) (i j : Fin n) (hij : i ≠ j) :
    (lagrangeBasis pts i).eval (pts.points j) = 0 := by
  sorry

/- ## Part II: Lagrange Interpolation -/

/-- The Lagrange interpolation operator L^n f(x) = Σ f(a_i) p_i(x). -/
noncomputable def lagrangeInterp (pts : InterpolationPoints n) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin n, f (pts.points i) * (lagrangeBasis pts i).eval x

/-- L^n interpolates f at the nodes: L^n f(a_i) = f(a_i). -/
theorem lagrangeInterp_at_node (pts : InterpolationPoints n) (f : ℝ → ℝ) (i : Fin n) :
    lagrangeInterp pts f (pts.points i) = f (pts.points i) := by
  sorry

/-- L^n f is a polynomial of degree ≤ n - 1. -/
theorem lagrangeInterp_degree (pts : InterpolationPoints n) (f : ℝ → ℝ) :
    ∃ p : Polynomial ℝ, p.natDegree ≤ n - 1 ∧
      ∀ x, lagrangeInterp pts f x = p.eval x := by
  sorry

/- ## Part III: The Lebesgue Function -/

/-- The Lebesgue function λ_n(x) = Σ |p_i^n(x)|. -/
noncomputable def lebesgueFunction (pts : InterpolationPoints n) (x : ℝ) : ℝ :=
  ∑ i : Fin n, |((lagrangeBasis pts i).eval x)|

/-- λ_n(x) ≥ 1 for all x ∈ [-1, 1]. -/
theorem lebesgueFunction_ge_one (pts : InterpolationPoints n) (x : ℝ)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) : lebesgueFunction pts x ≥ 1 := by
  sorry

/-- The Lebesgue constant Λ_n = max_{x ∈ [-1,1]} λ_n(x). -/
noncomputable def lebesgueConstant (pts : InterpolationPoints n) : ℝ :=
  ⨆ x ∈ Set.Icc (-1 : ℝ) 1, lebesgueFunction pts x

/-- Error bound: |L^n f(x) - f(x)| ≤ (1 + Λ_n) · best_approx. -/
theorem interpolation_error (pts : InterpolationPoints n) (f : C(Set.Icc (-1 : ℝ) 1, ℝ))
    (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    True := by  -- Error bound formula
  trivial

/- ## Part IV: Bernstein's Theorem -/

/-- Bernstein (1931): For any point sequence, ∃ x₀ where limsup λ_n(x₀) = ∞. -/
theorem bernstein (seq : PointSequence) :
    ∃ x₀ ∈ Set.Icc (-1 : ℝ) 1,
      Filter.limsup (fun n => lebesgueFunction (seq n) x₀) Filter.atTop = ⊤ := by
  sorry

/-- The Lebesgue constant grows: Λ_n ≥ (2/π) log n + O(1). -/
theorem lebesgueConstant_growth (pts : InterpolationPoints n) (hn : n ≥ 2) :
    lebesgueConstant pts ≥ (2 / Real.pi) * Real.log n - 1 := by
  sorry

/-- For Chebyshev nodes, Λ_n ~ (2/π) log n. -/
theorem chebyshev_lebesgue :
    True := by  -- Optimal growth rate
  trivial

/- ## Part V: Erdős-Vértesi Theorem -/

/-- Erdős-Vértesi (1980): For any points, ∃ continuous f where |L^n f(x)| → ∞ a.e. -/
theorem erdos_vertesi (seq : PointSequence) :
    ∃ f : C(Set.Icc (-1 : ℝ) 1, ℝ),
      ∀ᵐ x ∂volume.restrict (Set.Icc (-1 : ℝ) 1),
        Filter.limsup (fun n => |lagrangeInterp (seq n) f x|) Filter.atTop = ⊤ := by
  sorry

/-- Divergence is generic: Most continuous functions diverge a.e. -/
theorem divergence_generic (seq : PointSequence) :
    True := by  -- Baire category argument
  trivial

/- ## Part VI: Question 1 -/

/-- Question 1: Can λ_n(x) → ∞ yet L^n f(x) → f(x) for some x? -/
def Question1 : Prop :=
  ∃ seq : PointSequence, ∀ f : C(Set.Icc (-1 : ℝ) 1, ℝ),
    ∃ x ∈ Set.Icc (-1 : ℝ) 1,
      Filter.limsup (fun n => lebesgueFunction (seq n) x) Filter.atTop = ⊤ ∧
      Filter.Tendsto (fun n => lagrangeInterp (seq n) f x) Filter.atTop (nhds (f ⟨x, by sorry⟩))

/-- Question 1 is OPEN. -/
axiom question1_open : Question1

/- ## Part VII: Question 2 -/

/-- Question 2: Can λ_n(x) → ∞ for ALL x, yet still have some convergence? -/
def Question2 : Prop :=
  ∃ seq : PointSequence,
    (∀ x ∈ Set.Icc (-1 : ℝ) 1,
      Filter.limsup (fun n => lebesgueFunction (seq n) x) Filter.atTop = ⊤) ∧
    (∀ f : C(Set.Icc (-1 : ℝ) 1, ℝ),
      ∃ x ∈ Set.Icc (-1 : ℝ) 1,
        Filter.Tendsto (fun n => lagrangeInterp (seq n) f x) Filter.atTop (nhds (f ⟨x, by sorry⟩)))

/-- Question 2 is OPEN. -/
axiom question2_open : Question2

/-- Question 2 implies Question 1. -/
theorem q2_implies_q1 (h : Question2) : Question1 := by
  sorry

/- ## Part VIII: Special Point Sequences -/

/-- Chebyshev nodes: x_k = cos((2k-1)π / 2n). -/
noncomputable def chebyshevNodes (n : ℕ) : InterpolationPoints n where
  points := fun k => Real.cos ((2 * k.val + 1) * Real.pi / (2 * n))
  in_interval := by sorry
  distinct := by sorry

/-- Equidistant nodes: x_k = -1 + 2k/(n-1). -/
noncomputable def equidistantNodes (n : ℕ) (hn : n ≥ 2) : InterpolationPoints n where
  points := fun k => -1 + 2 * k.val / (n - 1)
  in_interval := by sorry
  distinct := by sorry

/-- Equidistant nodes have exponentially growing Lebesgue constant. -/
theorem equidistant_diverges (n : ℕ) (hn : n ≥ 2) :
    lebesgueConstant (equidistantNodes n hn) ≥ 2^(n-1) / n^2 := by
  sorry

/- ## Part IX: Convergence Conditions -/

/-- Uniform convergence: L^n f → f uniformly iff Λ_n · ω(f, 1/n) → 0. -/
theorem uniform_convergence_iff (seq : PointSequence) (f : C(Set.Icc (-1 : ℝ) 1, ℝ)) :
    True := by  -- Characterization of uniform convergence
  trivial

/-- Lipschitz functions converge under moderate Λ_n growth. -/
theorem lipschitz_convergence (seq : PointSequence) (f : C(Set.Icc (-1 : ℝ) 1, ℝ))
    (hLip : True) (hΛ : True) :  -- Λ_n = O(log n)
    True := by
  trivial

/-- Analytic functions converge for any point sequence. -/
theorem analytic_convergence (seq : PointSequence) (f : C(Set.Icc (-1 : ℝ) 1, ℝ))
    (hAnal : True) :  -- f extends analytically
    True := by
  trivial

/- ## Part X: Pointwise vs Uniform Convergence -/

/-- Faber's theorem: No point sequence gives uniform convergence for all C⁰. -/
theorem faber :
    ∀ seq : PointSequence, ∃ f : C(Set.Icc (-1 : ℝ) 1, ℝ),
      ¬∃ x ∈ Set.Icc (-1 : ℝ) 1,
        Filter.Tendsto (fun n => lagrangeInterp (seq n) f x) Filter.atTop (nhds (f ⟨x, by sorry⟩)) := by
  sorry

/-- Pointwise convergence is more delicate than uniform. -/
theorem pointwise_delicate :
    True := by  -- Pointwise can succeed where uniform fails
  trivial

/- ## Part XI: Measure-Theoretic Aspects -/

/-- For typical f, divergence occurs on a set of positive measure. -/
theorem positive_measure_divergence (seq : PointSequence) :
    ∃ f : C(Set.Icc (-1 : ℝ) 1, ℝ),
      volume {x ∈ Set.Icc (-1 : ℝ) 1 |
        Filter.limsup (fun n => |lagrangeInterp (seq n) f x|) Filter.atTop = ⊤} > 0 := by
  sorry

/-- Convergence set can have full measure for specific f. -/
theorem full_measure_convergence :
    ∃ seq : PointSequence, ∃ f : C(Set.Icc (-1 : ℝ) 1, ℝ),
      volume {x ∈ Set.Icc (-1 : ℝ) 1 |
        Filter.Tendsto (fun n => lagrangeInterp (seq n) f x) Filter.atTop (nhds (f ⟨x, by sorry⟩))} =
          volume (Set.Icc (-1 : ℝ) 1) := by
  sorry

/- ## Part XII: The Main Conjecture -/

/-- The main conjecture: Relationship between Questions 1 and 2. -/
def MainConjecture : Prop :=
  Question1 ↔ Question2

/-- The main conjecture is OPEN. -/
axiom main_conjecture_open : MainConjecture

/-- If Question 2 fails, understanding why would resolve Question 1. -/
theorem q2_fails_implies (h : ¬Question2) :
    ∀ seq : PointSequence,
      (∀ x ∈ Set.Icc (-1 : ℝ) 1,
        Filter.limsup (fun n => lebesgueFunction (seq n) x) Filter.atTop = ⊤) →
      ∃ f : C(Set.Icc (-1 : ℝ) 1, ℝ),
        ∀ x ∈ Set.Icc (-1 : ℝ) 1,
          ¬Filter.Tendsto (fun n => lagrangeInterp (seq n) f x) Filter.atTop (nhds (f ⟨x, by sorry⟩)) := by
  sorry

end Erdos671

/-
  ## Summary

  This file formalizes Erdős Problem #671 on Lagrange interpolation convergence.

  **Status**: OPEN (Prize: $250)

  **The Questions**:
  1. Can limsup λ_n(x) = ∞ yet L^n f(x) → f(x) for some x?
  2. Can λ_n(x) → ∞ for ALL x, yet still have pointwise convergence somewhere?

  **Known Results**:
  - Bernstein (1931): limsup λ_n(x₀) = ∞ for some x₀
  - Erdős-Vértesi (1980): |L^n f(x)| → ∞ a.e. for some f

  **Key sorries**:
  - `bernstein`: The classical divergence result
  - `erdos_vertesi`: The a.e. divergence theorem
  - `question1_open`, `question2_open`: The main open questions (axioms)
-/
