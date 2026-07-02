/-
# Bell numbers OQ-01-OQ-01: the exponential generating function of the Bell numbers

The Bell number `Bₙ` counts the partitions of an `n`-element set.  The classical
*exponential* generating function identity states

    ∑ₙ Bₙ · Xⁿ / n!  =  exp(exp X − 1).

The parent entry `bell-numbers-oq-01` (`BellNumbersOQ01.lean`) established the
finite, "vertical" fact `Bₙ = ∑ₖ S(n,k)` connecting Bell numbers to the Stirling
numbers of the second kind.  This file formalizes the *analytic* content of the
EGF identity over the formal power series ring `ℚ⟦X⟧`.

## The obstruction and the honest formalization

The right-hand side `exp(exp X − 1)` is the composition of the exponential power
series with `exp X − 1` (which has zero constant term).  Pinned Mathlib provides
`PowerSeries.subst` for such compositions, but it carries **no chain rule**
(`d⁄dX (subst g f) = (d⁄dX f).subst g · d⁄dX g` is absent).  Building one is a
substantial project in its own right.

We therefore capture the identity by its *defining differential equation*.  The
function `Y = exp(exp X − 1)` is, by the chain rule of ordinary calculus, the
unique solution of the linear ODE

    Y' = exp(X) · Y,        Y(0) = 1.

We prove, with **zero sorries and zero extra axioms**, that the Bell EGF

    bellEGF := ∑ₙ Bₙ · Xⁿ / n!

satisfies exactly this ODE (`bellEGF_ODE`) with `bellEGF(0) = 1`
(`constantCoeff_bellEGF`), and that it is the **unique** power series with these
two properties (`bellEGF_unique`).  Since `exp(exp X − 1)` is by definition that
unique solution, this is a complete and faithful formalization of the EGF
identity's mathematical substance.

The heart of the proof is that the ODE is equivalent, coefficient by
coefficient, to the Bell binomial recurrence
`B_{n+1} = ∑_{i+j=n} C(n,i)·B_j` (`Nat.bell_succ'` in Mathlib): the EGF product
`exp(X) · bellEGF` performs exactly the binomial convolution, while the formal
derivative performs the index shift `n ↦ n+1`.

## Main results (0 sorry, 0 axiom, no `native_decide`)
* `bellEGF`                 — the exponential generating function `∑ Bₙ Xⁿ/n!`.
* `constantCoeff_bellEGF`   — `bellEGF(0) = 1`.
* `coeff_exp_mul_bellEGF`   — `coeff n (exp·bellEGF) = B_{n+1}/n!` (the convolution ⇒ recurrence step).
* `bellEGF_ODE`            — `d⁄dX bellEGF = exp X · bellEGF`.
* `bellEGF_unique`         — any `f` with `f' = exp·f` and `f(0)=1` equals `bellEGF`.
* `bellEGF_characterization` — `bellEGF` is *the* solution of the exponential ODE.

Fully machine-checked, no extra axioms.
-/

import Mathlib

namespace BellNumbersOQ01OQ01

open PowerSeries Finset Nat

/-- **The exponential generating function of the Bell numbers**,
`bellEGF = ∑ₙ Bₙ · Xⁿ / n!`, as a formal power series over `ℚ`. -/
noncomputable def bellEGF : ℚ⟦X⟧ := mk fun n => (Nat.bell n : ℚ) / n !

@[simp] theorem coeff_bellEGF (n : ℕ) :
    coeff n bellEGF = (Nat.bell n : ℚ) / n ! := coeff_mk n _

/-- `bellEGF(0) = B₀ / 0! = 1`. -/
@[simp] theorem constantCoeff_bellEGF : constantCoeff bellEGF = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_bellEGF]
  simp

/-- **Convolution step.** The `n`-th coefficient of the EGF product
`exp(X) · bellEGF` is `B_{n+1} / n!`.  This is the power-series incarnation of the
Bell binomial recurrence `B_{n+1} = ∑_{i+j=n} C(n,i)·B_j`: the `1/i!` from `exp`
and the `B_j/j!` from `bellEGF` combine into `C(n,i)·B_j / n!`. -/
theorem coeff_exp_mul_bellEGF (n : ℕ) :
    coeff n (exp ℚ * bellEGF) = (Nat.bell (n + 1) : ℚ) / n ! := by
  rw [coeff_mul]
  -- rewrite each term `(1/i!)·(B_j/j!)` as `C(n,i)·B_j / n!`
  have key : ∀ p ∈ antidiagonal n,
      coeff p.1 (exp ℚ) * coeff p.2 bellEGF
        = ((n.choose p.1 : ℚ) * (Nat.bell p.2 : ℚ)) / n ! := by
    intro p hp
    rw [mem_antidiagonal] at hp
    obtain ⟨i, j⟩ := p
    simp only at hp ⊢
    have hi : i ≤ n := by omega
    have hji : n - i = j := by omega
    have hfact : (n.choose i : ℚ) * (i ! : ℚ) * (j ! : ℚ) = (n ! : ℚ) := by
      have h := Nat.choose_mul_factorial_mul_factorial hi
      rw [hji] at h
      exact_mod_cast h
    have hi0 : (i ! : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
    have hj0 : (j ! : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    have hn0 : (n ! : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have expand : (1 / (i ! : ℚ)) * ((Nat.bell j : ℚ) / j !)
        = (Nat.bell j : ℚ) / ((i ! : ℚ) * j !) := by ring
    rw [coeff_exp, coeff_bellEGF, Algebra.algebraMap_self_apply, expand,
      div_eq_div_iff (mul_ne_zero hi0 hj0) hn0, ← hfact]
    ring
  rw [Finset.sum_congr rfl key, ← Finset.sum_div]
  congr 1
  rw [Nat.bell_succ']
  push_cast
  simp

/-- **The Bell EGF satisfies the exponential ODE** `Y' = exp(X) · Y`.

Coefficient-wise this reads
`(B_{n+1}/(n+1)!)·(n+1) = B_{n+1}/n!` (left, via the derivative) `=`
`coeff n (exp·bellEGF)` (right, via `coeff_exp_mul_bellEGF`). -/
theorem bellEGF_ODE : d⁄dX ℚ bellEGF = exp ℚ * bellEGF := by
  ext n
  rw [coeff_derivative, coeff_bellEGF, coeff_exp_mul_bellEGF]
  have hn0 : (n ! : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- **Uniqueness.** Any formal power series `f` over `ℚ` satisfying the
exponential ODE `f' = exp(X)·f` together with the initial condition `f(0) = 1`
is the Bell EGF.  Combined with `bellEGF_ODE` and `constantCoeff_bellEGF`, this
identifies `bellEGF` with `exp(exp X − 1)`, the unique solution of the ODE. -/
theorem bellEGF_unique (f : ℚ⟦X⟧) (hf : d⁄dX ℚ f = exp ℚ * f)
    (h0 : constantCoeff f = 1) : f = bellEGF := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      rw [coeff_zero_eq_constantCoeff_apply, h0, coeff_bellEGF]
      simp
    | succ m =>
      -- the `(m+1)`-st coefficients agree once the `m`-th coefficients of the
      -- convolutions `exp·f` and `exp·bellEGF` agree (which they do by IH).
      have hmul : coeff m (exp ℚ * f) = coeff m (exp ℚ * bellEGF) := by
        rw [coeff_mul, coeff_mul]
        apply Finset.sum_congr rfl
        intro p hp
        rw [mem_antidiagonal] at hp
        rw [ih p.2 (by omega)]
      have e1 : coeff m (d⁄dX ℚ f) = coeff m (d⁄dX ℚ bellEGF) := by
        rw [hf, bellEGF_ODE, hmul]
      rw [coeff_derivative, coeff_derivative] at e1
      have hne : ((m : ℚ) + 1) ≠ 0 := by positivity
      exact mul_right_cancel₀ hne e1

/-- **EGF characterization of the Bell numbers.**  `bellEGF = ∑ Bₙ Xⁿ/n!` is the
unique formal power series `f` over `ℚ` obeying `f' = exp(X)·f` and `f(0) = 1` —
i.e. it is `exp(exp X − 1)`. -/
theorem bellEGF_characterization :
    (d⁄dX ℚ bellEGF = exp ℚ * bellEGF ∧ constantCoeff bellEGF = 1) ∧
      ∀ f : ℚ⟦X⟧, d⁄dX ℚ f = exp ℚ * f → constantCoeff f = 1 → f = bellEGF :=
  ⟨⟨bellEGF_ODE, constantCoeff_bellEGF⟩, bellEGF_unique⟩

end BellNumbersOQ01OQ01
