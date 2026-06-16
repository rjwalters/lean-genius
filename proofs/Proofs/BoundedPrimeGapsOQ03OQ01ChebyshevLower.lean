/-
  Chebyshev lower bound — the single missing Mathlib ingredient for
  `bounded-prime-gaps-oq-03-oq-01-oq-01`.

  STATUS: build-gated ORPHAN (not imported by Proofs.lean). It exists as a
  turnkey target for a future build / Aristotle `prove_file` once a backend
  is available. Do NOT register in Proofs.lean until it compiles green.

  ## Why this file exists

  The open question for `BoundedPrimeGapsOQ03OQ01.lean` is exactly to discharge
  the standing axiom

      axiom diameter_upper_bound_exists :
        ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 2 ≤ k →
          (minAdmissibleDiameter k : ℝ) ≤ C * k * (Real.log k) ^ 2

  The reduction (see knowledge.md, Route B) is:

    • Take H = the k smallest primes p > k. It is admissible
      (`IsAdmissible H := ∀ p prime, (H.image (· % p)).card < p`):
        - prime p ≤ k: every element of H is a prime > k ≥ p, so residue 0
          is missing ⇒ |H mod p| ≤ p − 1 < p;
        - prime p > k: |H| = k < p ⇒ |H mod p| ≤ k < p.
    • Its diameter is (k-th prime > k) − (smallest prime > k). Bounding this by
      C·k·(log k)² needs ≥ k primes inside an interval of length C·k·(log k)²
      just above k, i.e. a LOWER bound on π.

  Mathlib v4.26.0 status (verified by grep of /private/tmp/mathlib-grep @ v4.26.0):

    • `Mathlib.NumberTheory.Chebyshev` ALREADY develops ψ and θ in full:
        Chebyshev.psi, Chebyshev.theta, theta_eq_log_primorial,
        theta_le_log4_mul_x, psi_le, psi_le_const_mul_self,
        abs_psi_sub_theta_le_sqrt_mul_log, psi_eq_theta_add_sum_theta, …
      — but EVERY bound in that file is an UPPER bound. There is NO θ/ψ lower
      bound anywhere in Mathlib. That single lower bound is the whole gap.
    • `Mathlib.NumberTheory.PrimeCounting`: only `primeCounting'_add_le`
      (upper bound on π) and `add_two_le_nth_prime` (lower bound on nth prime)
      — both wrong direction.

  ## The missing lemma (this file)

  A Chebyshev-strength LOWER bound on ψ. Classical elementary derivation
  (de Polignac / central binomial), with confirmed v4.26.0 hooks:

    1. log ((2n)! / (n!)²) = log C(2n,n).  Mathlib: `Nat.centralBinom`,
       `Nat.choose_central…`.
    2. log C(2n,n) ≤ ψ(2n):  C(2n,n) ∣ lcm(1,…,2n) and ψ(N) = log lcm(1,…,N);
       or via the de Polignac identity log(N!) = ∑_{d≤N} Λ(d)⌊N/d⌋ together with
       `ArithmeticFunction.vonMangoldt_sum : ∑ i ∈ n.divisors, Λ i = Real.log n`.
       (This step — connecting ψ to log C(2n,n) — is the ~80–150 line core that
       Mathlib does not yet package.)
    3. 4 ^ n ≤ (2n+1) · C(2n,n):  `Nat.four_pow_le_two_mul_add_one_mul_central_binom`
       (in `Mathlib/Data/Nat/Choose/Central.lean`); sharper
       `Nat.four_pow_lt_mul_centralBinom (n≥4)`.
    ⇒ ψ(2n) ≥ log C(2n,n) ≥ n·log 4 − log(2n+1) ≥ c·(2n) for large n.

  Downstream (cheap, once the lemma below holds):
    • θ(x) ≥ ψ(x) − 2√x·log x  via `abs_psi_sub_theta_le_sqrt_mul_log` ⇒ θ(x) ≥ c'·x.
    • θ(x) = ∑_{p≤x} log p ≤ π(x)·log x ⇒ π(x) ≥ θ(x)/log x ≥ c'·x/log x.
    • Count ≥ k primes in (k, k + C·k·(log k)²]; finish the admissible
      construction and discharge `diameter_upper_bound_exists`.

  This file states ONLY step (2)+(3) packaged as the ψ lower bound — the genuine
  Mathlib gap. Everything else above is downstream bookkeeping or already present.
-/
import Mathlib

open scoped ArithmeticFunction

namespace BoundedPrimeGapsOQ03OQ01.ChebyshevLower

/-- **The missing ingredient.** A Chebyshev-strength lower bound on the second
Chebyshev function `ψ(x) = ∑_{n ≤ x} Λ(n)`.

Mathlib v4.26.0 has the full `Chebyshev.psi` / `Chebyshev.theta` API but only
*upper* bounds (`Chebyshev.psi_le`, `Chebyshev.theta_le_log4_mul_x`). This
existential lower bound is the single piece Route B needs; it is a known
classical result (no creative insight required), hence a clean Aristotle /
future-build target.

Proof sketch: `ψ(2n) ≥ log C(2n,n) ≥ n·log 4 − log(2n+1)` via the central
binomial bound `Nat.four_pow_le_two_mul_add_one_mul_central_binom` and the
divisibility `C(2n,n) ∣ lcm(1,…,2n)` (equivalently the de Polignac identity and
`ArithmeticFunction.vonMangoldt_sum`). A positive constant works for all `x ≥ 2`
because `ψ` is monotone with `ψ 2 = Real.log 2 > 0` and `ψ x / x → 1`. -/
theorem chebyshev_psi_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 2 ≤ x → c * x ≤ Chebyshev.psi x := by
  sorry

/-- Derived θ lower bound (downstream of `chebyshev_psi_lower_bound` via
`Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`). Recorded here to document the
chain; not the core gap. -/
theorem chebyshev_theta_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → c * x ≤ Chebyshev.theta x := by
  sorry

end BoundedPrimeGapsOQ03OQ01.ChebyshevLower
