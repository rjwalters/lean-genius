/-!
# Erdős Problem #893 — Divisor Sum of Mersenne Numbers

Define f(n) = ∑_{k=1}^{n} τ(2^k − 1), where τ is the divisor
counting function.

Question: Does f(2n)/f(n) → ∞ as n → ∞?

Kovač–Luca (2025) proved that lim sup f(2n)/f(n) = ∞, ruling out
any finite limit. The full question of whether the limit is ∞
(i.e., lim inf also diverges) remains open.

Status: OPEN
Reference: https://erdosproblems.com/893
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! ## Definition -/

/-- The number of divisors of n. -/
def tau (n : ℕ) : ℕ := n.divisors.card

/-- f(n) = ∑_{k=1}^{n} τ(2^k − 1), the cumulative divisor count
    of Mersenne numbers. -/
def mersenneDivisorSum (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, tau (2 ^ k - 1)

/-- The ratio f(2n)/f(n). -/
noncomputable def mersenneDivisorRatio (n : ℕ) : ℝ :=
  (mersenneDivisorSum (2 * n) : ℝ) / (mersenneDivisorSum n : ℝ)

/-! ## Main Question -/

/-- **Erdős Problem #893**: Does f(2n)/f(n) → ∞ as n → ∞?
    This asks whether the divisor count of Mersenne numbers
    grows super-linearly in a cumulative sense. -/
axiom erdos_893_divergence :
  ∀ M : ℝ, M > 0 →
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      mersenneDivisorRatio n > M

/-! ## Known Results -/

/-- **Kovač–Luca (2025)**: lim sup f(2n)/f(n) = ∞. This rules
    out any finite limit. -/
axiom kovac_luca_unbounded :
  ∀ M : ℝ, M > 0 →
    ∃ n : ℕ, mersenneDivisorRatio n > M

/-- **Partial Result**: Kovač–Luca showed that the ratio f(2n)/f(n)
    is not bounded above, proving a weaker version of the conjecture.
    The gap is between lim sup = ∞ and lim = ∞. -/
axiom partial_result :
  ¬∃ B : ℝ, ∀ n : ℕ, mersenneDivisorRatio n ≤ B

/-! ## Context -/

/-- **No Simple Asymptotic Formula**: Erdős observed that f(n) likely
    has no simple asymptotic formula because it increases too fast
    and erratically, driven by the arithmetic of Mersenne numbers. -/
axiom no_simple_asymptotic : True

/-- **Connection to Mersenne Primes**: When 2^k − 1 is prime,
    τ(2^k − 1) = 2. The distribution of Mersenne primes heavily
    influences the growth of f(n). -/
axiom mersenne_prime_connection : True

/-- **Cambie's Heuristic**: Cambie independently found a heuristic
    argument suggesting the ratio diverges, which Kovač–Luca
    made rigorous for the lim sup. -/
axiom cambie_heuristic : True
