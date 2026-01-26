/-!
# Erdős Problem #513: Maximum Term of a Power Series

For a transcendental entire function f(z) = Σ aₙzⁿ, define:
  μ(r) = max_n |aₙ rⁿ|       (maximum term)
  M(r) = max_{|z|=r} |f(z)|   (maximum modulus)

Determine the greatest possible value of
  liminf_{r→∞} μ(r) / M(r)
over all transcendental entire functions.

Known:
- The value exceeds 1/2 (Kövári, unpublished)
- The value is at most 2/π - c for some c > 0 (Clunie–Hayman, 1964)
- Trivially lies in [0, 1]

Status: OPEN.

Reference: https://erdosproblems.com/513
-/

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.LiminfLimsup

/-! ## Definitions -/

/-- The maximum term μ(r, f) = sup_n |aₙ| · rⁿ for a power series with
    coefficients given by `a : ℕ → ℂ`. Axiomatized. -/
axiom maxTerm (a : ℕ → ℂ) (r : ℝ) : ℝ

/-- maxTerm is nonneg for r ≥ 0. -/
axiom maxTerm_nonneg (a : ℕ → ℂ) (r : ℝ) (hr : 0 ≤ r) :
  0 ≤ maxTerm a r

/-- The maximum modulus M(r, f) = sup_{|z|=r} |f(z)| for the entire
    function defined by `a`. Axiomatized. -/
axiom maxModulus (a : ℕ → ℂ) (r : ℝ) : ℝ

/-- maxModulus is nonneg for r ≥ 0. -/
axiom maxModulus_nonneg (a : ℕ → ℂ) (r : ℝ) (hr : 0 ≤ r) :
  0 ≤ maxModulus a r

/-- The ratio μ(r)/M(r). Returns 0 if M(r) = 0. -/
noncomputable def termModulusRatio (a : ℕ → ℂ) (r : ℝ) : ℝ :=
  if maxModulus a r = 0 then 0
  else maxTerm a r / maxModulus a r

/-- A sequence of coefficients defines a transcendental entire function:
    the power series converges everywhere, and it is not a polynomial. -/
def IsTranscendentalEntire (a : ℕ → ℂ) : Prop :=
  (∀ N : ℕ, ∃ n : ℕ, n > N ∧ a n ≠ 0)

/-! ## Known Results -/

/-- μ(r) ≤ M(r) always holds, so the ratio is at most 1. -/
axiom maxTerm_le_maxModulus (a : ℕ → ℂ) (r : ℝ) (hr : 0 ≤ r) :
  maxTerm a r ≤ maxModulus a r

/-- Kövári's lower bound: for every transcendental entire function,
    liminf_{r→∞} μ(r)/M(r) ≤ the supremum, and the supremum exceeds 1/2.
    Axiomatized as: there exists a transcendental entire function whose
    liminf of the ratio exceeds 1/2. -/
axiom kovari_lower_bound :
  ∃ a : ℕ → ℂ, IsTranscendentalEntire a ∧
    (1 : ℝ) / 2 < Filter.liminf (fun r => termModulusRatio a r) Filter.atTop

/-- Clunie–Hayman upper bound (1964): for every transcendental entire
    function, liminf_{r→∞} μ(r)/M(r) ≤ 2/π - c for some absolute c > 0. -/
axiom clunie_hayman_upper_bound :
  ∃ c : ℝ, 0 < c ∧
    ∀ a : ℕ → ℂ, IsTranscendentalEntire a →
      Filter.liminf (fun r => termModulusRatio a r) Filter.atTop ≤ 2 / Real.pi - c

/-! ## The Open Question -/

/-- Erdős Problem #513: Determine the exact value of
    sup { liminf_{r→∞} μ(r)/M(r) : f transcendental entire }.
    Formalized as the assertion that this supremum exists in (1/2, 2/π). -/
axiom erdos_513_exact_value :
  ∃ L : ℝ, (1 : ℝ) / 2 < L ∧ L < 2 / Real.pi ∧
    (∀ a : ℕ → ℂ, IsTranscendentalEntire a →
      Filter.liminf (fun r => termModulusRatio a r) Filter.atTop ≤ L) ∧
    (∀ ε : ℝ, 0 < ε →
      ∃ a : ℕ → ℂ, IsTranscendentalEntire a ∧
        L - ε < Filter.liminf (fun r => termModulusRatio a r) Filter.atTop)
