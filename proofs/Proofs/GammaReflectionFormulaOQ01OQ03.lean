import Mathlib

/-!
# The half-integer Gamma values: `Γ(n + 1/2) = (2n)!·√π / (4ⁿ·n!)`

The Gamma function takes a clean closed form at every half-integer.  Starting from
the single transcendental value `Γ(1/2) = √π` and the functional equation
`Γ(s + 1) = s·Γ(s)`, the value at `n + 1/2` is forced to be a **rational multiple of
`√π`**:

  `Γ(n + 1/2) = (2n)! / (4ⁿ · n!) · √π.`

Equivalently the ratio `Γ(n + 1/2) / Γ(1/2)` is the rational number `(2n)!/(4ⁿ n!)`,
which is also `(2n−1)!! / 2ⁿ` (the odd double factorial over a power of two).  So
while `Γ(1/2) = √π` is irrational, *all* the arithmetic of the half-integer Gamma
values is captured by elementary factorials.

Mathlib provides the ingredients — `Real.Gamma_one_half_eq` (`Γ(1/2) = √π`),
`Real.Gamma_add_one` (the functional equation), and the Legendre duplication formula
`Real.Gamma_mul_Gamma_add_half` — but **not** this explicit half-integer closed form.
This entry supplies it by induction on `n`: the base case is `Γ(1/2) = √π`, and the
step multiplies by `n + 1/2` via the functional equation, the factor `(n + 1/2)`
promoting `(2n)!/(4ⁿ n!)` to `(2n+2)!/(4ⁿ⁺¹ (n+1)!)` after one `ring` manipulation of
the factorial recurrences.

This refines `gamma-reflection-formula-oq-01` (OQ-03): the sibling `oq-01-oq-01`
established `B(1/2,1/2) = π` (equivalently `Γ(1/2)² = π`); here we climb the whole
half-integer ladder above `1/2`.
-/

namespace GammaReflectionFormulaOQ01OQ03

open Real

/-- **Closed form for the half-integer Gamma values.**
`Γ(n + 1/2) = (2n)! / (4ⁿ · n!) · √π` for every natural number `n`.

Proof by induction.  Base: `Γ(1/2) = √π` (`Real.Gamma_one_half_eq`) and the
coefficient is `0!/(1·0!) = 1`.  Step: `Γ((n+1) + 1/2) = (n + 1/2)·Γ(n + 1/2)` by the
functional equation `Real.Gamma_add_one`; substituting the inductive hypothesis and
expanding the factorial recurrences `(2n+2)! = (2n+2)(2n+1)(2n)!`, `(n+1)! = (n+1)·n!`,
`4ⁿ⁺¹ = 4·4ⁿ`, the identity closes by `field_simp`/`ring` — the factor `n + 1/2 =
(2n+1)/2` is exactly what the recurrence needs. -/
theorem gamma_nat_add_half (n : ℕ) :
    Real.Gamma ((n : ℝ) + 1 / 2)
      = ((2 * n).factorial : ℝ) / (4 ^ n * (n.factorial : ℝ)) * Real.sqrt π := by
  induction n with
  | zero => norm_num [Real.Gamma_one_half_eq]
  | succ k ih =>
    have hk : ((k : ℝ) + 1 / 2) ≠ 0 := by positivity
    have hidx : ((k + 1 : ℕ) : ℝ) + 1 / 2 = ((k : ℝ) + 1 / 2) + 1 := by push_cast; ring
    rw [hidx, Real.Gamma_add_one hk, ih]
    -- factorial / power recurrences, cast to ℝ
    have f1 : ((2 * (k + 1)).factorial : ℝ)
        = (2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1) * ((2 * k).factorial : ℝ) := by
      have he : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
      rw [he, Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
    have f2 : (((k + 1).factorial : ℝ)) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hpow : (4 : ℝ) ^ (k + 1) = 4 * 4 ^ k := by rw [pow_succ]; ring
    have hkfac : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have h4 : (4 : ℝ) ^ k ≠ 0 := by positivity
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    rw [f1, f2, hpow]
    field_simp
    ring

/-- The half-integer Gamma value as a **rational multiple of `Γ(1/2)`**:
`Γ(n + 1/2) = (2n)!/(4ⁿ n!) · Γ(1/2)`.  Makes explicit that the entire `n`-dependence
is the rational coefficient `(2n)!/(4ⁿ n!)`; the only transcendental ingredient is the
single value `Γ(1/2)`. -/
theorem gamma_nat_add_half_eq_mul_gamma_half (n : ℕ) :
    Real.Gamma ((n : ℝ) + 1 / 2)
      = ((2 * n).factorial : ℝ) / (4 ^ n * (n.factorial : ℝ)) * Real.Gamma (1 / 2) := by
  rw [Real.Gamma_one_half_eq]; exact gamma_nat_add_half n

/-- **Positivity** of the half-integer Gamma values: `0 < Γ(n + 1/2)`.  Immediate from
the closed form, since `(2n)!`, `4ⁿ`, `n!` and `√π` are all positive. -/
theorem gamma_nat_add_half_pos (n : ℕ) : 0 < Real.Gamma ((n : ℝ) + 1 / 2) := by
  rw [gamma_nat_add_half]
  apply mul_pos
  · apply div_pos
    · exact_mod_cast Nat.factorial_pos (2 * n)
    · exact mul_pos (by positivity) (by exact_mod_cast Nat.factorial_pos n)
  · exact Real.sqrt_pos.mpr Real.pi_pos

/-- Worked value `Γ(3/2) = √π / 2`, the `n = 1` instance.  Derived independently from
the functional equation as a cross-check: `Γ(3/2) = Γ(1/2 + 1) = (1/2)·Γ(1/2)`. -/
theorem gamma_three_half : Real.Gamma (3 / 2) = Real.sqrt π / 2 := by
  rw [show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Real.Gamma_one_half_eq]
  ring

/-- Worked value `Γ(5/2) = 3√π / 4`, the `n = 2` instance: `Γ(5/2) = (3/2)·Γ(3/2)`. -/
theorem gamma_five_half : Real.Gamma (5 / 2) = 3 * Real.sqrt π / 4 := by
  rw [show (5 : ℝ) / 2 = 3 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    gamma_three_half]
  ring

/-- Consistency of the general formula with the worked value: instantiating
`gamma_nat_add_half` at `n = 1` reproduces `Γ(3/2) = √π / 2`. -/
theorem gamma_nat_add_half_one :
    Real.Gamma (((1 : ℕ) : ℝ) + 1 / 2) = Real.sqrt π / 2 := by
  rw [gamma_nat_add_half]
  norm_num [Nat.factorial]
  ring

end GammaReflectionFormulaOQ01OQ03
