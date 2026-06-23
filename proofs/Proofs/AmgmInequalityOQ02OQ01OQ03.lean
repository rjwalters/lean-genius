/-
  Newton-Girard k=3 Closed Form: p₃ = e₁³ − 3·e₁·e₂ + 3·e₃

  Open Question (amgm-inequality-oq-02-oq-01-oq-03):
  Establish the fully reduced k=3 Newton-Girard identity expressing the third power
  sum p₃ purely in terms of the elementary symmetric polynomials e₁, e₂, e₃:
      p₃ = e₁³ − 3·e₁·e₂ + 3·e₃.
  Over a Finset / for concrete values this is the classical sum-of-cubes formula
      a³ + b³ + c³ = (a+b+c)³ − 3·(a+b+c)·(ab+ac+bc) + 3·abc.

  Lineage:
  • Parent  amgm-inequality-oq-02-oq-01            : k=2 identity p₂ = e₁² − 2e₂
                                                     (concrete Finset, pair partition).
  • Sibling amgm-inequality-oq-02-oq-01-oq-02-oq-01: the *recurrence*
                                                     p₃ = e₁·p₂ − e₂·p₁ + 3·e₃ via
                                                     Mathlib's psum_eq_mul_esymm_sub_sum.

  This file closes the loop: substituting the closed forms p₂ = e₁² − 2e₂ and p₁ = e₁
  into the recurrence and simplifying yields the genuinely reduced k=3 identity, the
  universal (MvPolynomial) statement that specialises to every concrete Finset of
  values in any commutative ring. The explicit 3-variable case is included as the
  smallest concrete Finset instance.

  Status: PROVED (build-pending registration) — 0 sorries, 0 axioms.
  Tags: algebra, symmetric-functions, newton-girard, power-sums, finset
-/

import Mathlib
import Proofs.AmgmInequalityOQ02OQ01OQ02OQ01

namespace AMGMInequalityOQ02OQ01OQ03

open MvPolynomial Finset BigOperators

-- ============================================================
-- Universal closed form (MvPolynomial setting)
-- ============================================================

section Universal

variable (σ : Type*) (R : Type*) [CommRing R] [Fintype σ]

/-- **Newton-Girard k=3, closed form** (universal / MvPolynomial setting):
      p₃ = e₁³ − 3·(e₁·e₂) + 3·e₃.
    Derived from the recurrence `psum_three_eq` (p₃ = e₁·p₂ − e₂·p₁ + 3·e₃) by
    substituting the proven closed forms `psum_two_eq` (p₂ = e₁² − 2e₂) and
    `psum_one_eq_esymm_one` (p₁ = e₁), then ring-normalising.

    Every concrete instance — any finite family of values in any commutative ring —
    follows from this by evaluating the polynomial variables. -/
theorem psum_three_closed :
    psum σ R 3 =
      esymm σ R 1 ^ 3 - 3 * (esymm σ R 1 * esymm σ R 2) + 3 * esymm σ R 3 := by
  have h3 := AMGMInequalityOQ02OQ01OQ02OQ01.psum_three_eq σ R
  have h2 := AMGMInequalityOQ02OQ01OQ02OQ01.psum_two_eq σ R
  have h1 := AMGMInequalityOQ02OQ01OQ02OQ01.psum_one_eq_esymm_one σ R
  rw [h3, h2, h1]; ring

end Universal

-- ============================================================
-- Concrete Finset instance (smallest case, n = 3)
-- ============================================================

section Concrete

variable {R : Type*} [CommRing R]

/-- **Concrete 3-variable instance** — the classical sum-of-cubes factorisation:
      a³ + b³ + c³ = (a+b+c)³ − 3·(a+b+c)·(ab+ac+bc) + 3·abc.
    This is the n=3 Finset case of `psum_three_closed`, where
      e₁ = a+b+c, e₂ = ab+ac+bc, e₃ = abc, p₃ = a³+b³+c³. -/
theorem cube_sum_three (a b c : R) :
    a ^ 3 + b ^ 3 + c ^ 3 =
      (a + b + c) ^ 3 - 3 * ((a + b + c) * (a * b + a * c + b * c)) + 3 * (a * b * c) := by
  ring

end Concrete

end AMGMInequalityOQ02OQ01OQ03
