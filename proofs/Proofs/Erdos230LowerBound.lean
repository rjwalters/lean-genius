/-
Erdős Problem #230 — Discharging the √n lower bound axiom

The main file `Erdos230Problem.lean` records the "trivial" lower bound
`‖P‖_∞ ≥ √n` as an *axiom* (`supNorm_ge_l2norm`), justified informally by
Parseval's identity.  In that file the L²-norm is *defined* to be √n, so the
axiom is really the harmonic-analysis fact that the sup norm over the unit
circle dominates the L² norm.

This file removes the need for that axiom by replacing the analytic
(continuous) Parseval argument with the **elementary discrete** one:

  Averaging |P(ω)|² over the n-th roots of unity ω gives exactly n·(Σ|aₖ|²) = n²,
  so some root ω* satisfies |P(ω*)|² ≥ n, hence |P(ω*)| ≥ √n.

Because that root lies on the unit circle, the supremum over the circle is at
least √n.  This file proves every step of that reduction that does **not**
require the roots-of-unity orthogonality computation:

  * `evaluate_norm_le`           — ‖P(z)‖ ≤ n on the unit circle (triangle ineq.)
  * `bddAbove_supNorm_family`    — the family defining `supNormOnCircle` is
                                   bounded above (needed for `le_ciSup`)
  * `norm_ge_sqrt_of_normSq_ge`  — |w| ≥ √r from |w|² ≥ r
  * `supNorm_ge_of_witness`      — a single circle point with ‖P(z₀)‖ ≥ √n
                                   forces `supNormOnCircle P ≥ √n`

The remaining input — existence of a root ω* with |P(ω*)|² ≥ n (discrete
Parseval) — is the one genuinely computational lemma; it is isolated as the
hypothesis `exists_root_normSq_ge` and, once supplied, `supNorm_ge_sqrt`
discharges the axiom completely (see `supNorm_ge_sqrt_of`).
-/

import Mathlib
import Proofs.Erdos230Problem

namespace Erdos230.LowerBound

open Erdos230 Complex Finset

/-- **Upper bound on the unit circle.**
For `‖z‖ = 1`, the triangle inequality gives `‖P(z)‖ ≤ Σ‖aₖ‖ = n`. -/
theorem evaluate_norm_le {n : ℕ} (P : UnimodularPolynomial n) (z : ℂ)
    (hz : ‖z‖ = 1) : ‖evaluate P z‖ ≤ n := by
  unfold evaluate
  calc ‖∑ k : Fin n, P.coeffs k * z ^ (k.val + 1)‖
      ≤ ∑ k : Fin n, ‖P.coeffs k * z ^ (k.val + 1)‖ := norm_sum_le _ _
    _ = ∑ _k : Fin n, (1 : ℝ) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [norm_mul, norm_pow, P.unimodular k, hz, one_pow, mul_one]
    _ = n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_one]

/-- **Boundedness of the supremum family.**
The function `z ↦ ⨆_{‖z‖=1} ‖P(z)‖` whose supremum defines `supNormOnCircle`
is bounded above by `n`: on the circle by `evaluate_norm_le`, off the circle
the inner supremum is over the empty index and equals `0`. -/
theorem bddAbove_supNorm_family {n : ℕ} (P : UnimodularPolynomial n) :
    BddAbove (Set.range (fun z : ℂ => ⨆ (_ : ‖z‖ = 1), ‖evaluate P z‖)) := by
  refine ⟨n, ?_⟩
  rintro x ⟨z, rfl⟩
  -- `Real.iSup_le` handles the Prop-indexed supremum uniformly: on the circle
  -- each term is ≤ n by `evaluate_norm_le`, and the bound n is nonnegative.
  exact Real.iSup_le (fun hz => evaluate_norm_le P z hz) (by positivity)

/-- **From a modulus-squared bound to a modulus bound.** -/
theorem norm_ge_sqrt_of_normSq_ge {w : ℂ} {r : ℝ}
    (h : r ≤ Complex.normSq w) : Real.sqrt r ≤ ‖w‖ := by
  rw [Complex.normSq_eq_norm_sq] at h
  calc Real.sqrt r ≤ Real.sqrt (‖w‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = ‖w‖ := Real.sqrt_sq (norm_nonneg w)

/-- **The witness bridge.**
A single point `z₀` on the unit circle with `‖P(z₀)‖ ≥ √n` already forces the
supremum over the whole circle to be at least `√n`. -/
theorem supNorm_ge_of_witness {n : ℕ} (P : UnimodularPolynomial n) (z₀ : ℂ)
    (hz₀ : ‖z₀‖ = 1) (hge : Real.sqrt n ≤ ‖evaluate P z₀‖) :
    Real.sqrt n ≤ supNormOnCircle P := by
  unfold supNormOnCircle
  have hbdd := bddAbove_supNorm_family P
  calc Real.sqrt n
      ≤ ‖evaluate P z₀‖ := hge
    _ = ⨆ (_ : ‖z₀‖ = 1), ‖evaluate P z₀‖ := (ciSup_pos hz₀).symm
    _ ≤ ⨆ (z : ℂ), ⨆ (_ : ‖z‖ = 1), ‖evaluate P z‖ := le_ciSup hbdd z₀

/-- **Reduction of the lower-bound axiom to discrete Parseval.**
Given the existence of a root `ω*` of the unit circle with `|P(ω*)|² ≥ n`
(the discrete-Parseval witness), the sup-norm lower bound `‖P‖_∞ ≥ √n` —
i.e. the content of the axiom `Erdos230.supNorm_ge_l2norm` — follows with no
further assumptions. -/
theorem supNorm_ge_sqrt_of {n : ℕ} (P : UnimodularPolynomial n)
    (hwitness : ∃ z : ℂ, ‖z‖ = 1 ∧ (n : ℝ) ≤ Complex.normSq (evaluate P z)) :
    Real.sqrt n ≤ supNormOnCircle P := by
  obtain ⟨z, hz, hge⟩ := hwitness
  exact supNorm_ge_of_witness P z hz (norm_ge_sqrt_of_normSq_ge hge)

end Erdos230.LowerBound
