/-
Erdős Problem #975: Divisor Sums over Polynomial Values

Let f ∈ ℤ[x] be an irreducible non-constant polynomial such that f(n) ≥ 1 for
all sufficiently large n. Does there exist a constant c = c(f) > 0 such that

  Σ_{n ≤ x} τ(f(n)) ~ c · x · log(x)

where τ is the divisor counting function?

**Status**:
- OPEN in general
- SOLVED for irreducible quadratic polynomials (Hooley, 1963)
- Known bounds: x log x ≪ Σ τ(f(n)) ≪ x log x

**Key Results**:
- Van der Corput (1939): Lower bound Σ τ(f(n)) ≫ x log x
- Erdős (1952): Upper bound Σ τ(f(n)) ≪ x log x using elementary methods
- Hooley (1963): Asymptotic formula for quadratic polynomials
- McKee (1995-1999): Explicit constants for quadratics via Hurwitz class numbers

**Famous Example**: Σ_{n ≤ x} τ(n² + 1) = (3/π) x log x + O(x)

References:
- https://erdosproblems.com/975
- Van der Corput, J.G. (1939) "Une inégalité relative au nombre des diviseurs"
- Erdős, P. (1952) "On the sum Σ d(f(k))"
- Hooley, C. (1963) "On the number of divisors of a quadratic polynomial"
- Tao, T. (2011) Blog post "Erdos' divisor bound"
-/

import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Order.Basic

open Nat Filter Polynomial Asymptotics Real
open scoped ArithmeticFunction Topology

namespace Erdos975

/-!
## Definitions

We define the divisor sum over polynomial values, which is the core object of study
in Erdős Problem #975.
-/

/--
The divisor counting function τ(n), which counts the number of positive
divisors of n. For example, τ(12) = 6 since 12 has divisors 1, 2, 3, 4, 6, 12.

In Mathlib, this is `Nat.card n.divisors`.
-/
def divisorCount (n : ℕ) : ℕ := n.divisors.card

/--
Sum of τ(f(n)) from n = 1 to ⌊x⌋ for a polynomial f with integer coefficients.

This is the central object of Erdős Problem #975. We sum the divisor counts
of f(1), f(2), ..., f(⌊x⌋).
-/
noncomputable def divisorSumPoly (f : ℤ[X]) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (divisorCount (f.eval ↑n).natAbs : ℝ)

/-!
## Known Bounds

Van der Corput (1939) and Erdős (1952) established that for any irreducible
polynomial f, the sum Σ τ(f(n)) grows like Θ(x log x).
-/

/--
**Van der Corput's Lower Bound (1939)**:
For any irreducible polynomial f with f(n) ≥ 1 eventually,
  Σ_{n ≤ x} τ(f(n)) ≫ x log x

This shows the divisor sum grows at least as fast as x log x.
-/
axiom vanDerCorput_lower_bound (f : ℤ[X]) (hf : Irreducible f) (hdeg : f.natDegree ≠ 0)
    (hpos : ∀ᶠ n : ℕ in atTop, 1 ≤ f.eval (n : ℤ)) :
    (fun x => x * Real.log x) =O[atTop] divisorSumPoly f

/--
**Erdős's Upper Bound (1952)**:
For any irreducible polynomial f with f(n) ≥ 1 eventually,
  Σ_{n ≤ x} τ(f(n)) ≪ x log x

This shows the divisor sum grows at most as fast as x log x.
Erdős proved this using elementary (non-analytic) methods.
-/
axiom erdos_upper_bound (f : ℤ[X]) (hf : Irreducible f)
    (hpos : ∀ᶠ n : ℕ in atTop, 1 ≤ f.eval (n : ℤ)) :
    divisorSumPoly f =O[atTop] (fun x => x * Real.log x)

/-!
## Main Conjecture (Open)

The full Erdős Problem #975 asks whether there exists an asymptotic formula
with a specific constant c = c(f) > 0.
-/

/--
**Erdős Problem #975** (Open Conjecture):
For every irreducible non-constant polynomial f ∈ ℤ[x] with f(n) ≥ 1 eventually,
there exists a constant c = c(f) > 0 such that

  Σ_{n ≤ x} τ(f(n)) ~ c · x · log(x)

meaning the ratio converges to c as x → ∞.

While bounds of the form Θ(x log x) are known, proving the existence of a
specific limiting constant for general polynomials remains open.
-/
axiom erdos_975 : ∀ f : ℤ[X], f.natDegree ≠ 0 → Irreducible f →
    (∀ᶠ n : ℕ in atTop, 1 ≤ f.eval (n : ℤ)) →
    ∃ c : ℝ, 0 < c ∧ Tendsto (fun x => divisorSumPoly f x / (x * Real.log x)) atTop (nhds c)

/-!
## Solved Case: Quadratic Polynomials

Hooley (1963) resolved the conjecture for irreducible quadratic polynomials.
-/

/--
**Hooley's Theorem (1963)**:
For any irreducible quadratic polynomial f ∈ ℤ[x] with f(n) ≥ 1 eventually,
there exists c = c(f) > 0 such that Σ τ(f(n)) ~ c · x · log(x).

The constant c depends on the polynomial in a complicated way involving
Hurwitz class numbers and the discriminant of the polynomial.
-/
axiom hooley_quadratic (f : ℤ[X]) (hf : Irreducible f) (hdeg : f.natDegree = 2)
    (hpos : ∀ᶠ n : ℕ in atTop, 1 ≤ f.eval (n : ℤ)) :
    ∃ c : ℝ, 0 < c ∧ Tendsto (fun x => divisorSumPoly f x / (x * Real.log x)) atTop (nhds c)

/-!
## Famous Example: f(n) = n² + 1

The polynomial n² + 1 is irreducible over ℤ, and its divisor sum has the
beautiful asymptotic formula with constant 3/π.
-/

/-- The polynomial n² + 1 in ℤ[X]. -/
noncomputable def poly_n2_plus_1 : ℤ[X] := X ^ 2 + 1

/-- n² + 1 is irreducible over ℤ. -/
axiom irreducible_n2_plus_1 : Irreducible poly_n2_plus_1

/--
**The n² + 1 Asymptotic**:
  Σ_{n ≤ x} τ(n² + 1) = (3/π) · x · log(x) + O(x)

The constant 3/π ≈ 0.9549 arises from deep number-theoretic considerations
involving the distribution of prime factors of values of n² + 1.
-/
axiom n2_plus_1_asymptotic :
    Tendsto (fun x => divisorSumPoly poly_n2_plus_1 x / (x * Real.log x)) atTop (nhds (3 / π))

/--
The stronger form: the error term is O(x).
-/
axiom n2_plus_1_strong :
    (fun x => divisorSumPoly poly_n2_plus_1 x - (3 / π) * x * Real.log x) =O[atTop] id

/-!
## Basic Properties of Divisor Count
-/

/-- τ(1) = 1 (1 has exactly one divisor: itself). -/
theorem divisorCount_one : divisorCount 1 = 1 := by
  simp [divisorCount, Nat.divisors_one]

/-- τ(2) = 2 (divisors: 1, 2). -/
theorem divisorCount_two : divisorCount 2 = 2 := by
  simp [divisorCount]
  native_decide

/-- τ(6) = 4 (divisors: 1, 2, 3, 6). -/
theorem divisorCount_six : divisorCount 6 = 4 := by
  simp [divisorCount]
  native_decide

/-- τ(12) = 6 (divisors: 1, 2, 3, 4, 6, 12). -/
theorem divisorCount_twelve : divisorCount 12 = 6 := by
  simp [divisorCount]
  native_decide

/-- For prime p, τ(p) = 2. -/
theorem divisorCount_prime {p : ℕ} (hp : p.Prime) : divisorCount p = 2 := by
  simp only [divisorCount, Nat.Prime.divisors hp]
  rw [Finset.card_insert_of_not_mem, Finset.card_singleton]
  simp only [Finset.mem_singleton]
  exact hp.ne_one.symm

end Erdos975
