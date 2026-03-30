/-
  Harmonic Divergence OQ-04: Cauchy Condensation Test

  Oresme's proof that Σ 1/n diverges groups terms in blocks of powers of 2:
  (1/1) + (1/2) + (1/3 + 1/4) + (1/5+...+1/8) + ...
  ≥ (1/1) + (1/2) + (1/2) + (1/2) + ...

  This generalizes to the **Cauchy condensation test**:
  For f : ℕ → ℝ non-negative and decreasing,
    Σ f(n) converges ⟺ Σ 2^n · f(2^n) converges.

  This characterizes divergence for monotone sequences with terms → 0.
-/
import Mathlib

namespace HarmonicDivergenceOQ04

open Finset

/-- The partial sum Σ_{k=1}^n f(k). -/
noncomputable def partialSum (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k in Finset.range n, f (k + 1)

/-- The condensed partial sum Σ_{k=0}^n 2^k · f(2^k). -/
noncomputable def condensedSum (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k in Finset.range n, 2 ^ k * f (2 ^ k)

/-- **Cauchy Condensation Test (forward direction)**:
    If f is non-negative and decreasing, then
    Σ_{k=1}^{2^n - 1} f(k) ≤ Σ_{k=0}^{n-1} 2^k · f(2^k).

    Proof: Group terms in blocks [2^k, 2^{k+1}). In each block,
    f(j) ≤ f(2^k) for j ≥ 2^k (since f is decreasing).
    The block has 2^k terms, so the block sum ≤ 2^k · f(2^k). -/
theorem cauchy_condensation_upper (f : ℕ → ℝ) (n : ℕ)
    (hf_nn : ∀ k, 0 ≤ f k)
    (hf_decr : ∀ j k, j ≤ k → f k ≤ f j) :
    partialSum f (2 ^ n - 1) ≤ condensedSum f n := by
  sorry

/-- **Cauchy Condensation Test (reverse direction)**:
    If f is non-negative and decreasing, then
    Σ_{k=0}^{n-1} 2^k · f(2^k) ≤ f(1) + 2 · Σ_{k=1}^{2^{n-1}} f(k).

    Proof: 2^k · f(2^k) ≤ 2 · Σ_{j=2^{k-1}+1}^{2^k} f(j) for k ≥ 1
    (since f(2^k) ≤ f(j) for 2^{k-1} < j ≤ 2^k). -/
theorem cauchy_condensation_lower (f : ℕ → ℝ) (n : ℕ)
    (hf_nn : ∀ k, 0 ≤ f k)
    (hf_decr : ∀ j k, j ≤ k → f k ≤ f j)
    (hn : n ≥ 1) :
    condensedSum f n ≤ f 1 + 2 * partialSum f (2 ^ (n - 1)) := by
  sorry

/-- Application: Σ 1/n^p converges ⟺ p > 1.
    The condensed series is Σ 2^n · (2^n)^{-p} = Σ 2^{n(1-p)}.
    This is geometric with ratio 2^{1-p}: converges iff 2^{1-p} < 1 iff p > 1. -/
def p_series_convergence_characterization : Prop :=
  ∀ (p : ℝ), p > 0 →
    (∃ L : ℝ, Filter.Tendsto (partialSum (fun n => 1 / (n : ℝ) ^ p)) Filter.atTop (nhds L))
    ↔ p > 1

end HarmonicDivergenceOQ04
