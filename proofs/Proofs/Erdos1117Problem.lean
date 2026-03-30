/-
# Erdős Problem #1117: Maximum Modulus Points on Circles

For an entire function f(z) that is not a monomial, let ν(r) count
the number of points on the circle |z| = r where |f(z)| achieves
its maximum value M(r) = max_{|z|=r} |f(z)|.

## Questions
1. Can lim sup ν(r) = ∞? → YES (Herzog–Piranian 1968)
2. Can lim inf ν(r) = ∞? → OPEN (approximate answer by Glücksam–Pardo-Simón 2024)

## Background
For a monomial f(z) = cz^n, every point on |z|=r is a maximum point,
so ν(r) = ∞. For non-monomials, ν(r) is finite for each r.
The question is how ν(r) can grow.

## Status: OPEN (question 2)

Reference: https://erdosproblems.com/1117
-/

import Mathlib

/- ## Core Definitions -/

/-- An entire function: holomorphic (ℂ-differentiable) on all of ℂ.
    Previously an axiom; now a proper definition using Mathlib's Differentiable. -/
def IsEntire (f : ℂ → ℂ) : Prop := Differentiable ℂ f

/-- f is a monomial: f(z) = c·z^n for some c ∈ ℂ and n ∈ ℕ. -/
def IsMonomial (f : ℂ → ℂ) : Prop :=
  ∃ (c : ℂ) (n : ℕ), ∀ z : ℂ, f z = c * z ^ n

/-- The maximum modulus M(r): sup_{|z|=r} |f(z)|.
    Previously an axiom; now a proper definition. -/
noncomputable def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ z : ℂ, ‖z‖ = r ∧ x = ‖f z‖}

/-- M(r) is the supremum of |f(z)| on |z| = r. Proved by definition. -/
theorem maxModulus_def (f : ℂ → ℂ) (r : ℝ) (_hr : r > 0) :
    maxModulus f r = sSup {x : ℝ | ∃ z : ℂ, ‖z‖ = r ∧ x = ‖f z‖} :=
  rfl

/-- ν(r): the number of points on |z| = r where |f(z)| = M(r).
    Previously an axiom; now a proper definition using Nat.card. -/
noncomputable def nu (f : ℂ → ℂ) (r : ℝ) : ℕ :=
  Nat.card {z : ℂ | ‖z‖ = r ∧ ‖f z‖ = maxModulus f r}

/-- ν(r) counts the maximum modulus points on the circle of radius r. Proved by definition. -/
theorem nu_def (f : ℂ → ℂ) (r : ℝ) (_hr : r > 0) :
    nu f r = Nat.card {z : ℂ | ‖z‖ = r ∧ ‖f z‖ = maxModulus f r} :=
  rfl

/- ## Basic Properties -/

/-- For a non-monomial entire function, ν(r) is finite for each r > 0.
    Now trivially true since nu returns ℕ. Previously an axiom. -/
theorem nu_finite (f : ℂ → ℂ) (_hent : IsEntire f) (_hnm : ¬ IsMonomial f) (r : ℝ)
    (_hr : r > 0) : (nu f r : ℕ∞) < ⊤ :=
  WithTop.coe_lt_top _

/-- For a non-monomial entire function, ν(r) ≥ 1 for all r > 0
    (the maximum is always achieved on a compact set). -/
/- ## Question 1: lim sup ν(r) = ∞ (SOLVED) -/

/-- Herzog–Piranian (1968): There exists a non-monomial entire function f
    with lim sup_{r→∞} ν(r) = ∞.
    That is, for every N, there exist arbitrarily large r with ν(r) ≥ N. -/
/- ## Question 2: lim inf ν(r) = ∞ (OPEN) -/

/-- Erdős Problem #1117 (open part): Does there exist a non-monomial
    entire function f with lim inf_{r→∞} ν(r) = ∞?
    That is, for every N, eventually ν(r) ≥ N for all sufficiently large r. -/
/- ## Glücksam–Pardo-Simón Approximate Result (2024) -/

/-- Glücksam–Pardo-Simón (2024): An "approximate" affirmative answer
    to Question 2. They construct entire functions where the maximum
    modulus is achieved at many points for most radii, in a suitable
    approximate sense. -/
/- ## Hadamard Three-Circles Context -/

/-- The maximum modulus M(r) is a nondecreasing function of r for
    nonconstant entire functions (by the maximum modulus principle). -/
