/-
  Aristotle target for Erdős #230 — discrete Parseval witness.

  Goal: prove that for a unimodular polynomial of degree n ≥ 1 there is a point
  on the unit circle (an n-th root of unity) where |P(ω)|² ≥ n.

  Mathematical content (averaging over the n-th roots of unity ζ^j, j < n):
    Σ_{j<n} |P(ζ^j)|² = Σ_{j<n} Σ_{k,l} a_k conj(a_l) ζ^{j(k+1)} conj(ζ)^{j(l+1)}
                       = Σ_{k,l} a_k conj(a_l) Σ_{j<n} (ζ^{k+1} conj(ζ)^{l+1})^j.
  The inner geometric sum is n when k = l (the base is 1) and 0 otherwise
  (root-of-unity orthogonality, `geom_sum_eq` with base^n = 1, base ≠ 1).
  Hence the total is n · Σ_k |a_k|² = n · n = n², so the average over the n
  points is n and the maximum is ≥ n.

  This file separates that argument into two independent parts:

    * `exists_of_sum_normSq`    — the *averaging / pigeonhole* step.  If `n`
      unit-circle points carry total mass `Σ |P(pts j)|² = n²`, then one of them
      has `|P(z)|² ≥ n`.  This is elementary (no harmonic analysis) and is proved
      here in full.

    * `exists_roots_sum_normSq` — the *harmonic-analytic* input: existence of the
      n-th roots of unity together with the discrete-Parseval identity
      `Σ_j |P(ζ^j)|² = n²`.  This is the one genuinely computational lemma
      (root-of-unity orthogonality) and is isolated here as a `sorry`
      (Aristotle target).

  Combining them gives `exists_root_normSq_ge`, which
  `Erdos230.LowerBound.supNorm_ge_sqrt_of` turns into the sup-norm lower bound
  `‖P‖_∞ ≥ √n`, discharging the axiom `Erdos230.supNorm_ge_l2norm`.
-/

import Mathlib
import Proofs.Erdos230Problem

namespace Erdos230.Parseval

open Erdos230 Complex Finset

/-- **Averaging / pigeonhole step (elementary).**
If `n` points on the unit circle carry total squared mass `Σ_j |P(pts j)|² = n²`,
then at least one of them satisfies `|P(z)|² ≥ n`.  Pure averaging — no harmonic
analysis is used. -/
theorem exists_of_sum_normSq {n : ℕ} (hn : 1 ≤ n) (P : UnimodularPolynomial n)
    (pts : Fin n → ℂ) (hpts : ∀ j, ‖pts j‖ = 1)
    (hsum : ∑ j : Fin n, Complex.normSq (evaluate P (pts j)) = (n : ℝ) ^ 2) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ (n : ℝ) ≤ Complex.normSq (evaluate P z) := by
  by_contra h
  push_neg at h
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  -- every term is strictly below `n`, so the total is strictly below `n · n`
  have hlt : ∀ j : Fin n, Complex.normSq (evaluate P (pts j)) < (n : ℝ) :=
    fun j => h (pts j) (hpts j)
  have hsum_lt : ∑ j : Fin n, Complex.normSq (evaluate P (pts j))
      < ∑ _j : Fin n, (n : ℝ) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => hlt j)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum,
    pow_two] at hsum_lt
  exact lt_irrefl _ hsum_lt

/-- **Discrete Parseval identity (harmonic-analytic input).**
There exist `n` unit-circle points — the n-th roots of unity `ζ^j` — whose total
squared mass under `P` is exactly `n²`.  This packages the root-of-unity
orthogonality computation; it is the sole remaining computational obligation and
is left as the Aristotle target. -/
theorem exists_roots_sum_normSq {n : ℕ} (hn : 1 ≤ n) (P : UnimodularPolynomial n) :
    ∃ pts : Fin n → ℂ, (∀ j, ‖pts j‖ = 1) ∧
      ∑ j : Fin n, Complex.normSq (evaluate P (pts j)) = (n : ℝ) ^ 2 := by
  sorry

/-- **Discrete Parseval witness.**
For `n ≥ 1` and a unimodular polynomial `P` of degree `n`, some point on the
unit circle has `|P(z)|² ≥ n`.  Assembled from the averaging step
`exists_of_sum_normSq` and the discrete-Parseval identity
`exists_roots_sum_normSq`. -/
theorem exists_root_normSq_ge {n : ℕ} (hn : 1 ≤ n) (P : UnimodularPolynomial n) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ (n : ℝ) ≤ Complex.normSq (evaluate P z) := by
  obtain ⟨pts, hpts, hsum⟩ := exists_roots_sum_normSq hn P
  exact exists_of_sum_normSq hn P pts hpts hsum

end Erdos230.Parseval
