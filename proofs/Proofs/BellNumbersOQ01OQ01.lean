/-
# The exponential generating function of the Bell numbers

The Bell number `Bₙ` counts the partitions of an `n`-element set.  Their
exponential generating function has the famously compact closed form

    Σ_{n≥0} Bₙ xⁿ / n!  =  exp(exp x − 1).

Analytically, `E(x) = exp(exp x − 1)` is *the* function determined by the
first-order linear ODE

    E'(x) = exp(x) · E(x),      E(0) = 1,

because differentiating `exp(exp x − 1)` yields `exp(x)·exp(exp x − 1)` by the
chain rule, and `E(0) = exp(0) = 1`.  This file formalizes exactly this
characterization at the level of **formal power series over ℚ**, which is the
combinatorial heart of the EGF identity:

* `bellEGF` — the formal power series `Σ Bₙ Xⁿ/n!`.
* `constantCoeff_bellEGF` — `E(0) = 1`.
* `derivative_bellEGF` — the ODE `d⁄dX E = exp · E`.  This single identity is
  precisely the Bell binomial recurrence `B_{n+1} = Σ_i C(n,i) B_{n-i}`
  (Mathlib's `Nat.bell_succ'`) after clearing factorials.
* `ode_unique` — uniqueness of the power-series solution of `y' = exp·y`,
  `y(0)=1`; hence `bellEGF` **is** the formal series `exp(exp X − 1)`.

Pinned Mathlib carries `Nat.bell`, `PowerSeries.exp`, and the formal derivative
`PowerSeries.derivative`, but does not connect the Bell numbers to their
generating function.  This file fills that gap.  It does not rely on the
formal-substitution API (`PowerSeries.subst`); the literal identity
`bellEGF = subst (exp X − 1) exp` would additionally require a chain rule for
formal substitution, which pinned Mathlib lacks.

## Main results (0 sorry, 0 axiom)
* `constantCoeff_bellEGF`, `derivative_bellEGF`, `ode_unique`,
  `bellEGF_unique`.

Fully machine-checked, no extra axioms, no `native_decide`.
-/

import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic

namespace BellNumbersOQ01OQ01

open PowerSeries Finset

/-- The **exponential generating function of the Bell numbers**,
`E = Σ_{n} Bₙ Xⁿ / n!`, as a formal power series over `ℚ`. -/
noncomputable def bellEGF : PowerSeries ℚ :=
  PowerSeries.mk fun n => (Nat.bell n : ℚ) / n.factorial

@[simp] theorem coeff_bellEGF (n : ℕ) :
    PowerSeries.coeff n bellEGF = (Nat.bell n : ℚ) / n.factorial := by
  rw [bellEGF, PowerSeries.coeff_mk]

/-- `E(0) = 1`: the Bell EGF has constant term `B₀ = 1`. -/
theorem constantCoeff_bellEGF : PowerSeries.constantCoeff bellEGF = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_bellEGF]
  simp

/-- `coeff n (exp ℚ) = 1/n!`. -/
theorem coeff_exp_rat (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.exp ℚ) = 1 / n.factorial := by
  rw [PowerSeries.coeff_exp]
  simp

/-- **The defining ODE of the Bell EGF:** `d⁄dX E = exp · E`.

Coefficient-wise this says `B_{n+1}/n! = Σ_{i+j=n} (1/i!)·(B_j/j!)`, which after
multiplying by `n!` is the Bell binomial recurrence
`B_{n+1} = Σ_{i+j=n} C(n,i)·B_j` (`Nat.bell_succ'`). -/
theorem derivative_bellEGF :
    PowerSeries.derivative ℚ bellEGF = PowerSeries.exp ℚ * bellEGF := by
  ext n
  rw [PowerSeries.coeff_derivative, coeff_bellEGF, PowerSeries.coeff_mul]
  -- RHS: rewrite each factor
  simp only [coeff_exp_rat, coeff_bellEGF]
  -- Bring in the Bell recurrence, cast to ℚ.
  have hbs : (Nat.bell (n + 1) : ℚ)
      = ∑ p ∈ Finset.antidiagonal n, (n.choose p.1 : ℚ) * (Nat.bell p.2 : ℚ) := by
    have := Nat.bell_succ' n
    rw [this]
    push_cast
    rfl
  -- LHS = bell(n+1)/n!.
  have hfac : ((n : ℚ) + 1) / (↑(n + 1).factorial) = 1 / ↑n.factorial := by
    rw [Nat.factorial_succ]
    push_cast
    have hn : (n.factorial : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    field_simp
  rw [show (Nat.bell (n + 1) : ℚ) / ↑(n + 1).factorial * (↑n + 1)
        = (Nat.bell (n + 1) : ℚ) * ((↑n + 1) / ↑(n + 1).factorial) by ring,
     hfac, hbs, Finset.sum_mul]
  -- Term-by-term: (C(n,i)·B_j) · (1/n!) = (1/i!)·(B_j/j!) when i+j=n.
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_antidiagonal] at hp
  have hi : p.1 ≤ n := by omega
  have hchoose : (n.choose p.1 : ℚ) * (p.1.factorial : ℚ) * (p.2.factorial : ℚ)
      = (n.factorial : ℚ) := by
    have h := Nat.choose_mul_factorial_mul_factorial hi
    have hnp : n - p.1 = p.2 := by omega
    rw [hnp] at h
    exact_mod_cast h
  have hfi : (p.1.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p.1
  have hfj : (p.2.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p.2
  have hfn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp
  rw [← hchoose]
  ring

/-- **Uniqueness of the ODE solution.**  Any two formal power series over `ℚ`
with equal constant term and both satisfying `y' = exp · y` are equal.  The
`(n+1)`-st coefficient is forced by coefficients `0..n` through the ODE. -/
theorem ode_unique (f g : PowerSeries ℚ)
    (hf : PowerSeries.derivative ℚ f = PowerSeries.exp ℚ * f)
    (hg : PowerSeries.derivative ℚ g = PowerSeries.exp ℚ * g)
    (h0 : PowerSeries.constantCoeff f = PowerSeries.constantCoeff g) :
    f = g := by
  suffices h : ∀ n, PowerSeries.coeff n f = PowerSeries.coeff n g by
    ext n; exact h n
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
    | k + 1 =>
      -- The ODE at coefficient `k`, for both `f` and `g`.
      have ef : PowerSeries.coeff (k + 1) f * (↑k + 1)
          = PowerSeries.coeff k (PowerSeries.exp ℚ * f) := by
        rw [← PowerSeries.coeff_derivative, hf]
      have eg : PowerSeries.coeff (k + 1) g * (↑k + 1)
          = PowerSeries.coeff k (PowerSeries.exp ℚ * g) := by
        rw [← PowerSeries.coeff_derivative, hg]
      -- The product coefficient at `k` depends only on coefficients `≤ k`.
      have hmul : PowerSeries.coeff k (PowerSeries.exp ℚ * f)
          = PowerSeries.coeff k (PowerSeries.exp ℚ * g) := by
        rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.mem_antidiagonal] at hp
        rw [ih p.2 (by omega)]
      have hcancel : PowerSeries.coeff (k + 1) f * (↑k + 1)
          = PowerSeries.coeff (k + 1) g * (↑k + 1) := by
        rw [ef, hmul, ← eg]
      have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
      exact mul_right_cancel₀ hk1 hcancel

/-- **The Bell EGF is characterized by the ODE.**  `bellEGF` is the unique
formal power series over `ℚ` with constant term `1` satisfying `y' = exp·y`;
equivalently, `bellEGF` is the formal power series `exp(exp X − 1)`. -/
theorem bellEGF_unique (g : PowerSeries ℚ)
    (hg : PowerSeries.derivative ℚ g = PowerSeries.exp ℚ * g)
    (h0 : PowerSeries.constantCoeff g = 1) :
    g = bellEGF :=
  ode_unique g bellEGF hg derivative_bellEGF (by rw [h0, constantCoeff_bellEGF])

end BellNumbersOQ01OQ01
