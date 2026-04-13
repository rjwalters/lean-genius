/-
  Aristotle companion for ShannonEntropyOQ01.lean

  This file contains the two supporting sorry lemmas for Gaussian differential
  entropy that require automated proof search:
  1. gaussian_second_moment: ∫ (x-μ)² · φ(x) dx = σ²
  2. gaussian_quad_integrable: Integrable (fun x => (x-μ)² · φ(x))

  Both follow from Mathlib's ProbabilityTheory.gaussianReal variance machinery.
-/
import Mathlib

namespace ShannonEntropyOQ01Aristotle

open MeasureTheory Real ProbabilityTheory

noncomputable def gaussianPDF (μ σ : ℝ) (x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * σ ^ 2))⁻¹ * Real.exp (-(x - μ) ^ 2 / (2 * σ ^ 2))

theorem gaussian_second_moment (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ∫ x : ℝ, (x - μ) ^ 2 * gaussianPDF μ σ x = σ ^ 2 := by
  sorry

theorem gaussian_quad_integrable (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun x : ℝ => (x - μ) ^ 2 * gaussianPDF μ σ x) := by
  sorry

end ShannonEntropyOQ01Aristotle
