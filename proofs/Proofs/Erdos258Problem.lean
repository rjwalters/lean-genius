/-
Erdős Problem #258: Irrationality of Divisor Sum Series

**Problem**: Let $a_1, a_2, \ldots$ be a sequence of integers with $a_n \to \infty$.
Is the sum $\sum_n \frac{\tau(n)}{a_1 \cdots a_n}$ irrational, where $\tau(n)$ is the
number of divisors of $n$?

**Status**: The general problem is OPEN.

**Solved Variants**:
1. **Monotone case** (Erdős-Straus, 1971): If $(a_n)$ is monotone, the sum is irrational.
2. **Constant/power case** (Erdős, 1948): $\sum_n \frac{\tau(n)}{t^n}$ is irrational for $t \geq 2$.

Reference: https://erdosproblems.com/258
-/

import Mathlib.NumberTheory.Divisors
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.NumberTheory.Real.Irrational

open scoped BigOperators
open Nat Finset

namespace Erdos258

/-! ## Definitions -/

/-- The divisor function τ(n) counts the number of positive divisors of n.
    For example: τ(1) = 1, τ(6) = 4 (divisors: 1, 2, 3, 6), τ(p) = 2 for prime p. -/
def tau (n : ℕ) : ℕ := n.divisors.card

/-- The product a₁ · a₂ · ... · aₙ for a sequence a and index n.
    We use Finset.prod over the interval [1, n]. -/
def productPrefix (a : ℕ → ℕ) (n : ℕ) : ℕ := ∏ i ∈ Icc 1 n, a i

/-- The general term τ(n) / (a₁ · ... · aₙ) as a real number. -/
noncomputable def generalTerm (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (tau (n + 1) : ℝ) / (productPrefix a n : ℝ)

/-! ## Verified Computations -/

/-- τ(1) = 1: The only divisor of 1 is itself. -/
theorem tau_one : tau 1 = 1 := by native_decide

/-- τ(2) = 2: Divisors of 2 are 1 and 2. -/
theorem tau_two : tau 2 = 2 := by native_decide

/-- τ(6) = 4: Divisors of 6 are 1, 2, 3, 6. -/
theorem tau_six : tau 6 = 4 := by native_decide

/-- τ(12) = 6: Divisors of 12 are 1, 2, 3, 4, 6, 12. -/
theorem tau_twelve : tau 12 = 6 := by native_decide

/-- For prime p, τ(p) = 2 (divisors are 1 and p).
    We verify this for a few small primes. -/
theorem tau_prime_five : tau 5 = 2 := by native_decide
theorem tau_prime_seven : tau 7 = 2 := by native_decide

/-! ## Main Results -/

/--
**Erdős Problem #258 - Monotone Variant** (SOLVED):

If $(a_n)$ is a monotone sequence of positive integers with $a_n \to \infty$,
then $\sum_n \frac{\tau(n)}{a_1 \cdots a_n}$ is irrational.

This was proved by Erdős and Straus in 1971. The proof uses properties of
the divisor function and careful analysis of the convergence of the series.

We state this as an axiom since the proof requires deep number-theoretic
techniques beyond current Mathlib formalization.
-/
axiom erdos_258_monotone :
  ∀ (a : ℕ → ℕ),
    (∀ n, 0 < a n) →
    Monotone a →
    Filter.Tendsto a Filter.atTop Filter.atTop →
    Irrational (∑' n, generalTerm a n)

/--
**Erdős Problem #258 - Constant/Power Variant** (SOLVED):

For any integer $t \geq 2$, the sum $\sum_n \frac{\tau(n)}{t^n}$ is irrational.

This was proved by Erdős in 1948. The constant sequence case is simpler
because $a_1 \cdots a_n = t^n$, giving a series related to Lambert series.

We state this as an axiom since the proof involves transcendence techniques.
-/
axiom erdos_258_power :
  ∀ (t : ℕ), t ≥ 2 →
    Irrational (∑' n, (tau (n + 1) : ℝ) / (t : ℝ)^(n + 1))

/-! ## The Open Problem -/

/--
**Erdős Problem #258 - General Case** (OPEN):

The full conjecture asks: for ANY sequence $(a_n)$ with $a_n \to \infty$
(not necessarily monotone), is $\sum_n \frac{\tau(n)}{a_1 \cdots a_n}$ irrational?

This remains open. The monotone condition in the solved variant is essential
to the Erdős-Straus proof, and removing it introduces significant complications.
-/
def erdos_258_open_conjecture : Prop :=
  ∀ (a : ℕ → ℕ),
    (∀ n, 0 < a n) →
    Filter.Tendsto a Filter.atTop Filter.atTop →
    Irrational (∑' n, generalTerm a n)

/-! ## Properties of the Divisor Function -/

/-- τ(n) ≥ 1 for all positive n (at least the divisor 1).
    We verify this for small values. -/
theorem tau_pos_one : 0 < tau 1 := by native_decide
theorem tau_pos_two : 0 < tau 2 := by native_decide
theorem tau_pos_ten : 0 < tau 10 := by native_decide

end Erdos258
