/-!
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

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- An entire function: a function ℂ → ℂ that is holomorphic on all of ℂ. -/
axiom IsEntire (f : ℂ → ℂ) : Prop

/-- f is a monomial: f(z) = c·z^n for some c ∈ ℂ and n ∈ ℕ. -/
def IsMonomial (f : ℂ → ℂ) : Prop :=
  ∃ (c : ℂ) (n : ℕ), ∀ z : ℂ, f z = c * z ^ n

/-- The maximum modulus M(r): max_{|z|=r} |f(z)|. -/
axiom maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ

/-- M(r) is the supremum of |f(z)| on |z| = r. -/
axiom maxModulus_def (f : ℂ → ℂ) (r : ℝ) (hr : r > 0) :
    maxModulus f r = sSup {x : ℝ | ∃ z : ℂ, Complex.abs z = r ∧ x = Complex.abs (f z)}

/-- ν(r): the number of points on |z| = r where |f(z)| = M(r).
    For non-monomials, this is always finite (for each r). -/
axiom nu (f : ℂ → ℂ) (r : ℝ) : ℕ

/-- ν(r) counts the maximum modulus points on the circle of radius r. -/
axiom nu_def (f : ℂ → ℂ) (r : ℝ) (hr : r > 0) :
    nu f r = Nat.card {z : ℂ | Complex.abs z = r ∧ Complex.abs (f z) = maxModulus f r}

/-! ## Basic Properties -/

/-- For a non-monomial entire function, ν(r) is finite for each r > 0. -/
axiom nu_finite (f : ℂ → ℂ) (hent : IsEntire f) (hnm : ¬ IsMonomial f) (r : ℝ)
    (hr : r > 0) : nu f r < ⊤

/-- For a non-monomial entire function, ν(r) ≥ 1 for all r > 0
    (the maximum is always achieved on a compact set). -/
axiom nu_ge_one (f : ℂ → ℂ) (hent : IsEntire f) (r : ℝ) (hr : r > 0) :
    nu f r ≥ 1

/-! ## Question 1: lim sup ν(r) = ∞ (SOLVED) -/

/-- Herzog–Piranian (1968): There exists a non-monomial entire function f
    with lim sup_{r→∞} ν(r) = ∞.
    That is, for every N, there exist arbitrarily large r with ν(r) ≥ N. -/
axiom herzog_piranian (N : ℕ) :
    ∃ f : ℂ → ℂ, IsEntire f ∧ ¬ IsMonomial f ∧
      ∀ R : ℝ, ∃ r : ℝ, r > R ∧ nu f r ≥ N

/-! ## Question 2: lim inf ν(r) = ∞ (OPEN) -/

/-- Erdős Problem #1117 (open part): Does there exist a non-monomial
    entire function f with lim inf_{r→∞} ν(r) = ∞?
    That is, for every N, eventually ν(r) ≥ N for all sufficiently large r. -/
axiom erdos_1117_open :
    (∃ f : ℂ → ℂ, IsEntire f ∧ ¬ IsMonomial f ∧
      ∀ N : ℕ, ∃ R : ℝ, ∀ r : ℝ, r > R → nu f r ≥ N) ∨
    (∀ f : ℂ → ℂ, IsEntire f → ¬ IsMonomial f →
      ∃ N : ℕ, ∀ R : ℝ, ∃ r : ℝ, r > R ∧ nu f r < N)

/-! ## Glücksam–Pardo-Simón Approximate Result (2024) -/

/-- Glücksam–Pardo-Simón (2024): An "approximate" affirmative answer
    to Question 2. They construct entire functions where the maximum
    modulus is achieved at many points for most radii, in a suitable
    approximate sense. -/
axiom glucksam_pardo_simon_approximate :
    ∃ f : ℂ → ℂ, IsEntire f ∧ ¬ IsMonomial f ∧
      ∀ ε : ℝ, ε > 0 → ∀ N : ℕ, ∃ R : ℝ, ∀ r : ℝ, r > R →
        ∃ (S : Finset ℂ), S.card ≥ N ∧
          ∀ z ∈ S, Complex.abs z = r ∧
            Complex.abs (f z) ≥ (1 - ε) * maxModulus f r

/-! ## Hadamard Three-Circles Context -/

/-- The maximum modulus M(r) is a nondecreasing function of r for
    nonconstant entire functions (by the maximum modulus principle). -/
axiom maxModulus_nondecreasing (f : ℂ → ℂ) (hent : IsEntire f)
    (r₁ r₂ : ℝ) (h : 0 < r₁) (h12 : r₁ ≤ r₂) :
    maxModulus f r₁ ≤ maxModulus f r₂
