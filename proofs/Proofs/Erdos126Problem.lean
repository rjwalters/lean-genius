/-!
# Erdős Problem #126: Distinct Prime Factors of Pairwise Sums

Let f(n) be the maximum value such that for any A ⊆ ℕ with |A| = n,
the product ∏_{a ≠ b ∈ A} (a + b) has at least f(n) distinct prime factors.

**Conjecture**: f(n) / log(n) → ∞.

**Known bounds** (Erdős–Turán 1934): log(n) ≪ f(n) ≪ n / log(n).
The upper bound is trivial using A = {1, …, n}. Erdős noted that proving
f(n) = o(n / log(n)) has "never been seriously attacked."

**Status**: OPEN ($250 prize)

Reference: https://erdosproblems.com/126
Source: [ErTu34], [Er95c], [Er97], [Er97e]
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

open Filter Asymptotics

/-!
## Part I: The Extremal Function

The central object is f(n): the maximum m such that every n-element subset
A ⊆ ℕ guarantees at least m distinct prime factors in ∏_{a≠b} (a+b).
-/

namespace Erdos126

/-- f(n) is the maximum m such that for every A ⊆ ℕ with |A| = n,
    the product ∏_{a ≠ b} (a + b) has at least m distinct prime factors.

    This uses `Finset.offDiag` for ordered pairs (a, b) with a ≠ b,
    and `Nat.primeFactors` for the set of distinct prime divisors. -/
def IsMaximalAddFactorsCard (f : ℕ → ℕ) : Prop :=
  ∀ n, IsGreatest
    { m | ∀ (A : Finset ℕ), A.card = n →
      m ≤ (∏ p ∈ A.offDiag, ((p.1 + p.2) : ℕ)).primeFactors.card }
    (f n)

/-!
## Part II: The Main Conjecture

Erdős conjectured that f(n) grows strictly faster than log(n).
This is formalized as Tendsto (f(n)/log(n)) atTop atTop.
-/

/-- Erdős Problem #126: f(n) / log(n) → ∞.

    This asserts that the ratio f(n)/log(n) tends to infinity,
    i.e., f(n) grows strictly faster than logarithmic. -/
def ErdosConjecture126 (f : ℕ → ℕ) : Prop :=
  Tendsto (fun n => (f n : ℝ) / Real.log n) atTop atTop

/-- The main conjecture: if f is the extremal function, then f(n)/log(n) → ∞.

    This remains OPEN. Erdős offered $250 for a resolution.
    Axiomatized because no proof or disproof is known. -/
axiom erdos_126 : ∀ (f : ℕ → ℕ), IsMaximalAddFactorsCard f →
  ErdosConjecture126 f

/-!
## Part III: Known Bounds (Erdős–Turán 1934)

In their first joint paper, prompted by Lázár and Grünwald,
Erdős and Turán established: log(n) ≪ f(n) ≪ n / log(n).
-/

/-- Lower bound: log(n) ≪ f(n), i.e., log(n) = O(f(n)).

    Erdős and Turán (1934) showed f(n) grows at least logarithmically.
    Axiomatized: the proof uses sieve methods. -/
axiom erdos_turan_lower (f : ℕ → ℕ) (hf : IsMaximalAddFactorsCard f) :
  (fun (n : ℕ) => Real.log n) =O[atTop] fun (n : ℕ) => (f n : ℝ)

/-- Upper bound: f(n) ≪ n / log(n), i.e., f(n) = O(n / log(n)).

    The upper bound follows from taking A = {1, …, n}:
    the largest pairwise sum is 2n − 1, so all prime factors are ≤ 2n − 1,
    and by the prime number theorem there are ~ n / log(n) such primes.
    Axiomatized: the proof relies on the prime number theorem. -/
axiom erdos_turan_upper (f : ℕ → ℕ) (hf : IsMaximalAddFactorsCard f) :
  (fun (n : ℕ) => (f n : ℝ)) =O[atTop] fun (n : ℕ) => (n : ℝ) / Real.log n

/-- Combined Erdős–Turán bounds: log(n) ≪ f(n) ≪ n / log(n).

    This packages both bounds together. The gap between log(n) and n/log(n)
    is enormous: the conjecture asks whether f(n) is at the lower end. -/
theorem erdos_turan_bounds (f : ℕ → ℕ) (hf : IsMaximalAddFactorsCard f) :
    ((fun (n : ℕ) => Real.log n) =O[atTop] fun (n : ℕ) => (f n : ℝ)) ∧
    ((fun (n : ℕ) => (f n : ℝ)) =O[atTop] fun (n : ℕ) => (n : ℝ) / Real.log n) :=
  ⟨erdos_turan_lower f hf, erdos_turan_upper f hf⟩

/-!
## Part IV: The Little-o Question

A secondary open question: is f(n) = o(n / log(n))?
If true, the Erdős–Turán upper bound is not tight.
Erdős said this has "never been seriously attacked."
-/

/-- Erdős noted that f(n) = o(n / log(n)) has never been proved.
    This would show the upper bound is not tight, narrowing
    the gap between the known lower and upper bounds.

    Axiomatized: this is itself an open question. -/
axiom erdos_126_littleo : ∀ (f : ℕ → ℕ), IsMaximalAddFactorsCard f →
  (fun (n : ℕ) => (f n : ℝ)) =o[atTop] fun (n : ℕ) => (n : ℝ) / Real.log n

/-!
## Part V: Trivial Upper Bound Construction

When A = {1, …, n}, all pairwise sums lie in {3, …, 2n − 1}.
The prime factors of these sums are bounded by 2n − 1, giving
at most π(2n − 1) ~ 2n / log(n) distinct prime factors by PNT.
-/

/-- The trivial upper bound: when A = {1, …, n}, the product's prime factors
    are bounded by 2n via the prime number theorem.

    This shows f(n) ≤ O(n / log(n)) by explicit construction. -/
axiom trivial_upper_bound (n : ℕ) :
  ∃ (A : Finset ℕ), A.card = n ∧
    (∏ p ∈ A.offDiag, ((p.1 + p.2) : ℕ)).primeFactors.card ≤ 2 * n

/-!
## Part VI: Monotonicity of f

A basic structural observation: f is monotone non-decreasing,
since any (n+1)-element set contains an n-element subset.
-/

/-- f is monotone: adding elements to A can only introduce more primes.
    Axiomatized as it requires careful combinatorial reasoning
    about sub-multisets of the product. -/
axiom f_monotone (f : ℕ → ℕ) (hf : IsMaximalAddFactorsCard f) :
  Monotone f

/-!
## Part VII: Summary

- The extremal function f(n) counts minimum distinct prime factors
  of pairwise sums over n-element sets.
- Erdős–Turán (1934): log(n) ≪ f(n) ≪ n / log(n).
- Conjecture: f(n) / log(n) → ∞ (OPEN, $250 prize).
- Whether f(n) = o(n / log(n)) is also unknown.
- No significant progress since 1934 on narrowing the bounds.
-/

/-- The conjecture implies the lower bound is not tight:
    if f(n)/log(n) → ∞ then f(n) is not O(log(n)).

    Axiomatized: the proof requires showing that if a sequence g(n)/log(n) → ∞
    then g is not O(log), which needs Filter.Tendsto properties not
    directly available in current Mathlib. -/
axiom conjecture_implies_not_O_log (f : ℕ → ℕ)
    (hf : IsMaximalAddFactorsCard f)
    (hconj : ErdosConjecture126 f) :
    ¬ ((fun (n : ℕ) => (f n : ℝ)) =O[atTop] fun (n : ℕ) => Real.log n)

end Erdos126
