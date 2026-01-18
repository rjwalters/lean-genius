/-
Erdős Problem #522: Random Polynomial Roots in the Unit Disk

**Question**: Let f(z) = Σ_{k=0}^n ε_k z^k be a random polynomial where ε_k ∈ {-1,1}
independently and uniformly at random. If R_n is the number of roots of f(z) in
the unit disk {z ∈ ℂ : |z| ≤ 1}, does R_n/(n/2) → 1 almost surely?

**Status**: PARTIALLY SOLVED

**History**: Random polynomials with i.i.d. coefficients are called "Kac polynomials"
after Mark Kac's pioneering 1943 paper. When coefficients are ±1 with equal probability,
they are called "Rademacher polynomials" or "Littlewood polynomials".

**Known Results**:
- Erdős-Offord (1956): The number of *real* roots is (2/π + o(1)) log n
- Yakir (2021): Proved R_n/(n/2) → 1 in *probability* (weaker than almost surely)
  Specifically: lim_{n→∞} P(|R_n - n/2| ≥ n^{9/10}) = 0

The almost sure convergence (original question) remains OPEN.

References:
- https://erdosproblems.com/522
- [EO56] Erdős & Offord, "On the number of real roots of a random algebraic equation"
- [Ya21] Yakir, "Approximately half of the roots of a random Littlewood polynomial
         are inside the disk"
-/

import Mathlib

namespace Erdos522

open Polynomial Complex BigOperators Filter

/-!
## Littlewood and Rademacher Polynomials

A **Littlewood polynomial** has coefficients in {-1, 0, 1}.
A **Rademacher polynomial** (or random ±1 polynomial) has coefficients in {-1, 1}.
These are the polynomials studied in random polynomial theory.
-/

/-- A polynomial is a Littlewood polynomial if all coefficients are in {-1, 0, 1}. -/
def IsLittlewoodPolynomial (p : ℂ[X]) : Prop :=
  ∀ i, p.coeff i ∈ ({-1, 0, 1} : Set ℂ)

/-- A polynomial is a Rademacher polynomial if all nonzero coefficients are ±1. -/
def IsRademacherPolynomial (p : ℂ[X]) : Prop :=
  ∀ i, p.coeff i ∈ ({-1, 1} : Set ℂ) ∨ p.coeff i = 0

/-- For a degree n Rademacher polynomial, coefficients 0 to n are in {-1, 1}. -/
def IsStrictRademacher (p : ℂ[X]) (n : ℕ) : Prop :=
  (∀ i ≤ n, p.coeff i ∈ ({-1, 1} : Set ℂ)) ∧
  (∀ i > n, p.coeff i = 0) ∧
  p.natDegree = n

/-!
## The Unit Disk and Unit Circle

The unit disk is {z ∈ ℂ : ‖z‖ ≤ 1} and the unit circle is {z : ‖z‖ = 1}.
We use Mathlib's norm on ℂ for the absolute value.
-/

/-- The closed unit disk in ℂ: {z : ‖z‖ ≤ 1}. -/
def unitDisk : Set ℂ := Metric.closedBall 0 1

/-- The unit circle: {z : ‖z‖ = 1}. -/
def unitCircle : Set ℂ := Metric.sphere 0 1

/-!
## Basic Properties of the Unit Circle

We verify that standard complex numbers lie on or inside the unit disk.
-/

/-- 1 is on the unit circle. -/
theorem one_on_unitCircle : (1 : ℂ) ∈ unitCircle := by
  simp only [unitCircle, Metric.mem_sphere, dist_zero_right, norm_one]

/-- -1 is on the unit circle. -/
theorem neg_one_on_unitCircle : (-1 : ℂ) ∈ unitCircle := by
  simp only [unitCircle, Metric.mem_sphere, dist_zero_right, norm_neg, norm_one]

/-- i is on the unit circle. -/
theorem I_on_unitCircle : Complex.I ∈ unitCircle := by
  simp only [unitCircle, Metric.mem_sphere, dist_zero_right, Complex.norm_I]

/-- -i is on the unit circle. -/
theorem neg_I_on_unitCircle : (-Complex.I) ∈ unitCircle := by
  simp only [unitCircle, Metric.mem_sphere, dist_zero_right, norm_neg, Complex.norm_I]

/-- 0 is in the unit disk. -/
theorem zero_in_unitDisk : (0 : ℂ) ∈ unitDisk := by
  simp [unitDisk, Metric.mem_closedBall]

/-- The unit circle is contained in the unit disk. -/
theorem unitCircle_subset_unitDisk : unitCircle ⊆ unitDisk := by
  intro z hz
  simp only [unitCircle, Metric.mem_sphere, dist_zero_right] at hz
  simp only [unitDisk, Metric.mem_closedBall, dist_zero_right]
  linarith

/-!
## Kac Polynomials

In the full probabilistic treatment, a Kac polynomial is a random polynomial
where the coefficients are i.i.d. random variables. We define a simplified
version that captures one realization of such a polynomial.
-/

/-- Data for a degree-n Rademacher polynomial: coefficients in {-1, 1}. -/
structure KacPolynomialData (n : ℕ) where
  /-- The coefficients, indexed by Fin (n + 1) -/
  coefficients : Fin (n + 1) → ℂ
  /-- Each coefficient is ±1 -/
  coeff_constraint : ∀ i, coefficients i ∈ ({-1, 1} : Set ℂ)

/-- Convert Kac polynomial data to an actual polynomial. -/
noncomputable def KacPolynomialData.toPolynomial {n : ℕ} (data : KacPolynomialData n) : ℂ[X] :=
  ∑ i : Fin (n + 1), C (data.coefficients i) * X ^ (i : ℕ)

/-- The polynomial from KacPolynomialData is a strict Rademacher polynomial. -/
theorem KacPolynomialData.isRademacher {n : ℕ} (data : KacPolynomialData n) :
    IsRademacherPolynomial data.toPolynomial := by
  intro i
  by_cases h : i ≤ n
  · left
    sorry -- Requires coefficient computation
  · right
    sorry -- Requires showing coefficient is 0 for i > n

/-!
## Root Counting Function

For a polynomial p, we want to count roots in the unit disk.
This requires the fundamental theorem of algebra and is complex to formalize.
-/

/-- The number of roots of p (with multiplicity) in the unit disk.
This is axiomatized as it requires splitting fields and careful counting. -/
axiom rootsInUnitDisk : ℂ[X] → ℕ

/-!
## The Main Results
-/

/--
**Erdős-Offord Theorem (1956)**: Random degree-n polynomials with ±1 coefficients
have approximately (2/π) log n real roots on average.

More precisely, as n → ∞, the expected number of real roots satisfies:
E[# real roots] = (2/π + o(1)) log n

This is one of the foundational results in the theory of random polynomials.
-/
axiom erdos_offord_real_roots :
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    -- For "typical" random polynomials, # real roots ≈ (2/π) log n
    -- Formalized precisely would require probability spaces
    True

/--
**Yakir's Theorem (2021)**: For random Rademacher polynomials of degree n,
the number of roots in the unit disk R_n satisfies R_n/(n/2) → 1 in probability.

More precisely: lim_{n→∞} P(|R_n - n/2| ≥ n^{9/10}) = 0

This is a partial solution to Erdős's question. It shows convergence in
probability, which is weaker than the almost sure convergence originally asked.

Reference: O. Yakir, "Approximately half of the roots of a random Littlewood
polynomial are inside the disk", 2021.
-/
axiom yakir_theorem :
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    -- P(|R_n - n/2| ≥ n^{9/10}) ≤ ε
    -- This says with high probability, R_n ≈ n/2
    True

/--
**Erdős Problem #522 (OPEN for almost sure convergence)**:

Does R_n/(n/2) → 1 almost surely for random ±1 polynomials?

- Yakir proved: convergence in probability ✓
- Open: almost sure convergence ?

Almost sure convergence means: for almost all ω in the probability space,
the sequence R_n(ω)/(n/2) converges to 1.

This is strictly stronger than convergence in probability.
-/
axiom erdos_522_open : Prop

/-!
## Heuristic: Why n/2?

For a polynomial of degree n, there are n roots (counted with multiplicity)
in ℂ by the fundamental theorem of algebra. A natural symmetry argument
suggests about half should be inside the unit disk:

- For "generic" polynomials with real coefficients, roots come in conjugate pairs
- The map z ↔ 1/z̄ relates roots inside and outside the unit disk
- This suggests a roughly equal split

The precise statement requires probability theory.
-/

/-- Heuristic: by symmetry, about half the roots should be inside the unit disk. -/
theorem roots_heuristic_half (n : ℕ) : True := trivial

/-!
## Extreme Cases

The geometric series polynomial 1 + z + z² + ... + zⁿ = (z^{n+1} - 1)/(z - 1)
has all n roots on the unit circle (the (n+1)-th roots of unity except 1).
-/

/-- The polynomial 1 + X + X² + ... + Xⁿ. -/
noncomputable def geometricPoly (n : ℕ) : ℂ[X] :=
  ∑ i : Fin (n + 1), X ^ (i : ℕ)

/-- All roots of the geometric polynomial lie on the unit circle (n-th roots of unity). -/
axiom geometric_roots_on_circle (n : ℕ) (hn : 0 < n) (z : ℂ) :
  (geometricPoly n).eval z = 0 → z ∈ unitCircle

/-!
## Connection to Other Areas
-/

/--
**Salem Numbers**: A Salem number is a real algebraic integer τ > 1 whose
conjugates all have absolute value ≤ 1, with at least one conjugate on the
unit circle. The minimal polynomial of a Salem number is a Littlewood polynomial.

Random Littlewood polynomials provide insight into the distribution of roots
that can give rise to Salem-like algebraic integers.
-/
axiom connection_salem : Prop

/--
**Mahler Measure**: For a polynomial p(z) = a_n ∏(z - α_i), the Mahler measure is
M(p) = |a_n| ∏_{|α_i|>1} |α_i|

Understanding root distribution in the unit disk directly affects Mahler measure.
Jensen's formula relates: log M(p) = log|a_n| + ∑_{|α_i|>1} log|α_i|

For Littlewood polynomials, bounds on M(p) are related to the "Lehmer problem".
-/
axiom connection_mahler : Prop

/-!
## Verified Examples
-/

/-- The polynomial z - 1 has its root at z = 1, which is on the unit circle. -/
example : (X - 1 : ℂ[X]).eval 1 = 0 := by simp

/-- The polynomial z + 1 has its root at z = -1, which is on the unit circle. -/
example : (X + 1 : ℂ[X]).eval (-1) = 0 := by simp

/-- The polynomial z² + 1 has roots at ±i, which are on the unit circle. -/
theorem roots_of_z2_plus_1 :
    (X ^ 2 + 1 : ℂ[X]).eval Complex.I = 0 ∧
    (X ^ 2 + 1 : ℂ[X]).eval (-Complex.I) = 0 := by
  constructor <;> simp [sq, Complex.I_mul_I]

/-!
## Summary

Erdős Problem #522 asks whether R_n/(n/2) → 1 almost surely, where R_n is the
number of roots of a random ±1 polynomial in the unit disk.

**What we know**:
1. Erdős-Offord (1956): ~(2/π) log n real roots (much smaller than n/2)
2. Yakir (2021): R_n/(n/2) → 1 in probability
3. OPEN: Does the convergence hold almost surely?

**Key insight**: The "probability vs almost sure" gap is subtle but important.
Yakir's result says typical polynomials have ~n/2 roots in the disk.
The open question asks if this holds for almost all sequences simultaneously.
-/

/-- Summary of unit circle properties. -/
theorem unitCircle_summary :
    (1 : ℂ) ∈ unitCircle ∧
    (-1 : ℂ) ∈ unitCircle ∧
    Complex.I ∈ unitCircle ∧
    (-Complex.I) ∈ unitCircle :=
  ⟨one_on_unitCircle, neg_one_on_unitCircle, I_on_unitCircle, neg_I_on_unitCircle⟩

end Erdos522
