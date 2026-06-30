import Mathlib
import Proofs.ChebyshevBoundsOQ02OQ01
import Proofs.ChebyshevBoundsOQ02OQ02

/-
# Explicit Two-Sided Bounds on the Chebyshev θ Function

The first Chebyshev function `θ(n) = ∑_{p ≤ n} log p` is, like `ψ`, of linear
order `Θ(n)` — this is the elementary heart of the prime number theorem.

Mathlib provides the clean *upper* bound `Chebyshev.theta_le_log4_mul_x`
(`θ(x) ≤ log 4 · x`), but **no** matching lower bound for either `θ` or `ψ`.
The substantive lower estimate lives in this project:
`ChebyshevBoundsOQ02OQ01.chebyshevPsi_lower_linear` proves
`(log 2 / 3)·m ≤ ψ(m)` for `m ≥ 2` (from the central binomial coefficient).

Here we transfer that lower bound from `ψ` to `θ` using the closeness estimate
`ChebyshevBoundsOQ02OQ02.abs_psi_sub_theta_le`
(`|ψ(n) − θ(n)| ≤ 2·√n·log n`, Mathlib's `abs_psi_sub_theta_le_sqrt_mul_log`
via the project's bridge). Since `ψ` and `θ` differ by only `O(√n·log n)`, the
linear lower bound on `ψ` descends to `θ` up to that lower-order correction:

  `(log 2 / 3)·m − 2·√m·log m  ≤  θ(m)  ≤  log 4 · m`    for `m ≥ 2`.

This pins `θ(m) = Θ(m)` with explicit constants — a result stated nowhere in
Mathlib (which has only the upper half) and not previously assembled in this
project.
-/

namespace ChebyshevBoundsOQ02OQ01OQ01

open ChebyshevBoundsOQ02 ChebyshevBoundsOQ02OQ02

/--
**Explicit linear lower bound for `θ`.**

For `m ≥ 2`,
`(log 2 / 3)·m − 2·√m·log m ≤ θ(m)`.

Proof: `θ(m) = ψ(m) − (ψ(m) − θ(m))`. The lower bound
`(log 2 / 3)·m ≤ ψ(m)` (`chebyshevPsi_lower_linear`) and the closeness bound
`ψ(m) − θ(m) ≤ |ψ(m) − θ(m)| ≤ 2·√m·log m` (`abs_psi_sub_theta_le`) combine
linearly. The correction `2·√m·log m` is lower order, so for large `m` the bound
is `≈ (log 2 / 3)·m`, confirming `θ(m) = Θ(m)`.
-/
theorem chebyshevTheta_lower {m : ℕ} (hm : 2 ≤ m) :
    Real.log 2 / 3 * (m : ℝ) - 2 * Real.sqrt m * Real.log m ≤ chebyshevTheta m := by
  have hpsi : Real.log 2 / 3 * (m : ℝ) ≤ chebyshevPsi m :=
    ChebyshevBoundsOQ02OQ01.chebyshevPsi_lower_linear hm
  have hdiff : |chebyshevPsi m - chebyshevTheta m| ≤ 2 * Real.sqrt m * Real.log m :=
    ChebyshevBoundsOQ02OQ02.abs_psi_sub_theta_le m (by omega)
  have h1 : chebyshevPsi m - chebyshevTheta m ≤ 2 * Real.sqrt m * Real.log m :=
    (le_abs_self _).trans hdiff
  linarith

/--
**Explicit linear upper bound for `θ`.**

`θ(n) ≤ log 4 · n` for every `n`. This is Mathlib's `Chebyshev.theta_le_log4_mul_x`
transported through the project's bridge `chebyshevTheta_eq_mathlib`.
-/
theorem chebyshevTheta_upper (n : ℕ) :
    chebyshevTheta n ≤ Real.log 4 * (n : ℝ) := by
  rw [chebyshevTheta_eq_mathlib]
  exact Chebyshev.theta_le_log4_mul_x (by positivity)

/--
**Two-sided explicit Chebyshev `θ` bounds:**
`(log 2 / 3)·m − 2·√m·log m ≤ θ(m) ≤ log 4 · m` for `m ≥ 2`.

The elementary `θ(m) = Θ(m)` with both endpoints explicit: the upper bound is
Mathlib's `log 4 · m`, while the lower bound is obtained by descending this
project's `ψ` lower bound `(log 2 / 3)·m` across the `O(√m·log m)` gap between
`ψ` and `θ`. Mathlib supplies only the upper inequality, so the lower bound is
the new content.
-/
theorem chebyshevTheta_bounds {m : ℕ} (hm : 2 ≤ m) :
    Real.log 2 / 3 * (m : ℝ) - 2 * Real.sqrt m * Real.log m ≤ chebyshevTheta m ∧
      chebyshevTheta m ≤ Real.log 4 * (m : ℝ) :=
  ⟨chebyshevTheta_lower hm, chebyshevTheta_upper m⟩

end ChebyshevBoundsOQ02OQ01OQ01
