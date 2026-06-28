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

  This is a known, finite computation (ideal for proof search). Once proved,
  `Erdos230.LowerBound.supNorm_ge_sqrt_of` turns it into the sup-norm lower
  bound `‖P‖_∞ ≥ √n`, discharging the axiom `Erdos230.supNorm_ge_l2norm`.
-/

import Mathlib
import Proofs.Erdos230Problem

namespace Erdos230.Parseval

open Erdos230 Complex Finset

/-- **Discrete Parseval witness.**
For `n ≥ 1` and a unimodular polynomial `P` of degree `n`, some point on the
unit circle has `|P(z)|² ≥ n`. -/
theorem exists_root_normSq_ge {n : ℕ} (hn : 1 ≤ n) (P : UnimodularPolynomial n) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ (n : ℝ) ≤ Complex.normSq (evaluate P z) := by
  sorry

end Erdos230.Parseval
