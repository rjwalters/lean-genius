/-
# Erdős #490 — reducing the Chebyshev θ-gap axiom to a primorial-ratio bound

The main file `Erdos490Problem.lean` isolates a single analytic axiom

    chebyshev_theta_upper_half_lower_bound :
      ∃ c > 0, ∀ N ≥ 4, c * N ≤ Chebyshev.theta N − Chebyshev.theta (N/2)

which is the classical Chebyshev-strength lower bound on the θ-gap `θ(N) − θ(N/2) ≳ N`.
Mathlib's `Mathlib.NumberTheory.Chebyshev` supplies only *upper* bounds on `θ` and `ψ`, so
the lower bound must be built.

This companion file discharges the **analytic wrapper** of that axiom with a *verified*
(0-sorry) reduction: using Mathlib's `Chebyshev.theta_eq_log_primorial`, the θ-gap is
exactly `log (primorial N / primorial (N/2))`.  Hence eliminating the axiom is *precisely*
the elementary number-theoretic statement

    primorial_ratio_lower :
      ∃ c > 0, ∀ N ≥ 4, c * N ≤ log (primorial N / primorial (N/2)),

i.e. a lower bound on the product of primes in the upper half-interval `(N/2, N]`.  No
`Chebyshev.theta` remains in that goal — it is a pure `primorial` inequality, exactly the
Erdős central-binomial estimate.  The Mathlib pin (v4.26.0) now carries the **complete
Erdős toolkit** to prove it:

* `Nat.four_pow_lt_mul_centralBinom`  (`4^n < n · centralBinom n`, the lower bound on `C(2n,n)`)
* `Nat.prod_pow_factorization_centralBinom`  (`∏_{p≤2n} p^{v_p} = centralBinom n`)
* `Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul`  (primes in `(2n/3, n]` vanish)
* `Nat.pow_factorization_choose_le`  (`p^{v_p(C(2n,n))} ≤ 2n` for every prime)
* `Nat.factorization_choose_le_one`  (`p² > 2n ⟹ v_p ≤ 1`)
* `primorial_le_4_pow`  (the primorial upper bound `∏_{p≤m} p ≤ 4^m`)

so `primorial_ratio_lower` is a *buildable* (no longer blocked) multi-step central-binomial
argument, not a Mathlib gap.  It is isolated below as a single theorem sorry for Aristotle.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev

open scoped Nat
open Finset

namespace Erdos490ThetaGap

/-- **Analytic wrapper, verified (0-sorry).**  The Chebyshev θ-gap `θ(N) − θ(N/2)` equals
`log (primorial N / primorial (N/2))`.  Immediate from `Chebyshev.theta_eq_log_primorial`
(`θ x = log (primorial ⌊x⌋₊)`) and `Nat.floor_natCast`. -/
theorem theta_gap_eq_log_primorial_ratio (N : ℕ) :
    Chebyshev.theta (N : ℝ) - Chebyshev.theta ((N / 2 : ℕ) : ℝ)
      = Real.log ((primorial N : ℝ) / (primorial (N / 2) : ℝ)) := by
  rw [Chebyshev.theta_eq_log_primorial, Chebyshev.theta_eq_log_primorial,
    Nat.floor_natCast, Nat.floor_natCast,
    Real.log_div (by exact_mod_cast (primorial_pos N).ne')
      (by exact_mod_cast (primorial_pos (N / 2)).ne')]

/-- **The remaining core — the Erdős central-binomial θ-gap lower bound.**  A lower bound on
the product of primes in the upper half `(N/2, N]`, phrased purely via `primorial`.  This is
classical (Erdős's proof of Bertrand's postulate gives exactly this estimate) and buildable
from the Mathlib toolkit listed in the file header; it carries **no** `Chebyshev.theta`.
Isolated as a single theorem sorry, to be discharged by Aristotle (or by hand) once tooling
is available — the Erdős `√(2n)`-split plan is recorded in the problem's `knowledge.md`. -/
theorem primorial_ratio_lower :
    ∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, N ≥ 4 →
      c * (N : ℝ) ≤ Real.log ((primorial N : ℝ) / (primorial (N / 2) : ℝ)) := by
  sorry

/-- **The Chebyshev θ-gap lower bound, reduced to `primorial_ratio_lower` (0 new axioms).**
This is exactly the statement currently taken as `chebyshev_theta_upper_half_lower_bound` in
`Erdos490Problem.lean`; here it is *derived* from the pure-`primorial` core via the verified
analytic wrapper `theta_gap_eq_log_primorial_ratio`.  Once `primorial_ratio_lower` is proved,
this eliminates the last analytic axiom of Erdős #490. -/
theorem chebyshev_theta_gap_lower :
    ∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, N ≥ 4 →
      c * (N : ℝ) ≤ Chebyshev.theta (N : ℝ) - Chebyshev.theta ((N / 2 : ℕ) : ℝ) := by
  obtain ⟨c, hc, h⟩ := primorial_ratio_lower
  refine ⟨c, hc, fun N hN => ?_⟩
  rw [theta_gap_eq_log_primorial_ratio]
  exact h N hN

end Erdos490ThetaGap
