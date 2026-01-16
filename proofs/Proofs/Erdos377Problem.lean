/-
  Erdős Problem #377: Prime Factors Not Dividing Central Binomial

  **Conjecture**: Is there an absolute constant C > 0 such that
  ∑_{p ≤ n, p ∤ C(2n,n)} 1/p ≤ C for all n?

  **Status**: OPEN — the main conjecture remains unsolved.

  **Known Results** (Erdős-Graham-Ruzsa-Straus 1975):
  - The Cesàro mean of f(n) converges to γ₀ = ∑_{k≥2} log(k)/2^k
  - The second moment also converges: ∑f(n)²/x → γ₀²
  - For almost all n: f(n) = γ₀ + o(1)
  - Upper bound: f(n) ≤ c·log(log(n)) for some c < 1 and large n

  The function f(n) measures how many small primes "miss" the central binomial.

  Reference: https://erdosproblems.com/377
  Key paper: Erdős-Graham-Ruzsa-Straus, "On the prime factors of C(2n,n)" (1975)
-/

import Mathlib.Data.Nat.Choose.Central
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Order.Filter.Cofinite

namespace Erdos377

open Nat Finset Filter BigOperators
open scoped Topology

/-! ## The Main Function -/

/--
For a natural number n, `sumInvPrimesNotDivCentralBinom n` is the sum of 1/p
over all primes p ≤ n that do NOT divide C(2n, n).

This function measures how many "small" primes fail to divide the central binomial.
By Kummer's theorem, p divides C(2n,n) iff there's a carry in base-p addition n + n.
-/
noncomputable def sumInvPrimesNotDivCentralBinom (n : ℕ) : ℝ :=
  ∑ p ∈ Icc 1 n with p.Prime, if p ∣ n.centralBinom then 0 else (1 : ℝ) / p

/-! ## The Main Conjecture -/

/--
**Erdős Problem #377 (Open Conjecture)**: Is there an absolute constant C > 0 such that
∑_{p ≤ n, p ∤ C(2n,n)} 1/p ≤ C for all n?

Equivalently: is sumInvPrimesNotDivCentralBinom bounded?

Heuristically, "most" primes divide C(2n,n) for large n, so the sum of those that don't
might be uniformly bounded. But this is unproven.
-/
def BoundedConjectureHolds : Prop :=
  ∃ C > (0 : ℝ), ∀ (n : ℕ), sumInvPrimesNotDivCentralBinom n ≤ C

/-- The main open question -/
theorem erdos_377 : BoundedConjectureHolds ↔
    ∃ C > (0 : ℝ), ∀ (n : ℕ), sumInvPrimesNotDivCentralBinom n ≤ C := by
  rfl

/-! ## Known Results (EGRS 1975) -/

/--
The constant γ₀ = ∑_{k=2}^∞ log(k)/2^k that appears in the asymptotic behavior.
This is approximately 0.7943...
-/
noncomputable def gamma0 : ℝ := ∑' (k : ℕ), (k + 2 : ℝ).log / 2 ^ (k + 2)

/--
**EGRS 1975 - First Moment**: The Cesàro mean of f(n) converges to γ₀.
(1/x) ∑_{n ≤ x} f(n) → γ₀ as x → ∞

This shows f(n) is "typically" around γ₀.
-/
axiom egrs_first_moment :
    Tendsto (fun (x : ℕ) => (1 : ℝ) / x * ∑ n ∈ Icc 1 x, sumInvPrimesNotDivCentralBinom n)
      atTop (𝓝 gamma0)

/--
**EGRS 1975 - Second Moment**: The Cesàro mean of f(n)² converges to γ₀².
(1/x) ∑_{n ≤ x} f(n)² → γ₀² as x → ∞

Combined with the first moment, this implies f(n) concentrates around γ₀.
-/
axiom egrs_second_moment :
    Tendsto (fun (x : ℕ) =>
      (1 : ℝ) / x * ∑ n ∈ Icc 1 x, sumInvPrimesNotDivCentralBinom n ^ 2)
      atTop (𝓝 (gamma0 ^ 2))

/--
**EGRS 1975 - Almost Everywhere Result**: For almost all integers n,
f(n) = γ₀ + o(1).

This follows from the first two moments by a variance argument:
Var(f) = E[f²] - E[f]² → γ₀² - γ₀² = 0.
-/
axiom egrs_almost_everywhere :
    ∃ (o : ℕ → ℝ) (_ : Tendsto o atTop (𝓝 0)),
      ∀ᶠ n in cofinite, sumInvPrimesNotDivCentralBinom n = gamma0 + o n

/--
**EGRS 1975 - Upper Bound**: For some c < 1 and all large n,
f(n) ≤ c · log(log(n)).

This improves the trivial bound from Mertens' theorem which gives c = 1 + o(1).
-/
axiom egrs_upper_bound : ∃ c < (1 : ℝ),
    ∀ᶠ n in atTop, sumInvPrimesNotDivCentralBinom n ≤ c * (n : ℝ).log.log

/-! ## Understanding the Problem -/

/--
By Kummer's theorem, the largest power of prime p dividing C(2n,n) equals
the number of carries when adding n + n in base p.

A prime p does NOT divide C(2n,n) iff there are NO carries when adding n + n in base p,
which happens iff all digits of n in base p are less than p/2.
-/

/--
The sum over primes p that DO divide C(2n,n) is asymptotically log(log(n)).
This is the "complement" of f(n).
-/
noncomputable def sumInvPrimesDividingCentralBinom (n : ℕ) : ℝ :=
  ∑ p ∈ Icc 1 n with p.Prime, if p ∣ n.centralBinom then (1 : ℝ) / p else 0

/--
The two sums are complementary: they partition the sum over all primes ≤ n.
-/
theorem complementary_sums (n : ℕ) :
    sumInvPrimesNotDivCentralBinom n + sumInvPrimesDividingCentralBinom n =
    ∑ p ∈ Icc 1 n with p.Prime, (1 : ℝ) / p := by
  sorry -- Straightforward from the definitions

/-! ## Implications -/

/--
A positive answer to Problem #377 would imply that "most" of the prime reciprocal sum
comes from primes dividing C(2n,n):
∑_{p ≤ n, p | C(2n,n)} 1/p = (1 - o(1)) log(log(n))

EGRS say there is "no doubt" this is true.
-/

end Erdos377
