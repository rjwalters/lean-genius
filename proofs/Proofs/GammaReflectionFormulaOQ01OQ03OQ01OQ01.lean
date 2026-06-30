/-
# Gamma Reflection OQ-01-OQ-03-OQ-01-OQ-01: An *analytic* reproof of `(2n)! = (2n-1)‼·2ⁿ·n!`

**Open question (sibling `GammaReflectionFormulaOQ01OQ03OQ01`).** The sibling file proves
the factorial identity

> `(2n)! = (2n-1)‼ · 2ⁿ · n!`

by a purely **combinatorial** route — the factorial split `(2n)! = (2n)‼·(2n-1)‼`
together with `(2n)‼ = 2ⁿ·n!` (`Nat.doubleFactorial_two_mul`) — and uses it to convert the
central form of the half-integer Gamma value into the odd-double-factorial form.

This file does the **reverse**: it reproves the *same* arithmetic identity from the
**analytic** side, "from the Legendre/half-integer Gamma value", with no appeal to the
combinatorial bridge. The two pieces are:

* a *fresh* induction giving the double-factorial closed form
  `Γ(n+1/2) = (2n-1)‼·√π / 2ⁿ` directly from the functional equation
  `Γ(s+1) = s·Γ(s)` and `Γ(1/2) = √π` — **not** routed through the central form; and
* the parent's independently-derived central form
  `Γ(n+1/2) = (2n)!·√π / (4ⁿ·n!)` (`GammaReflectionFormulaOQ01OQ03.gamma_nat_add_half`).

Equating the two closed forms cancels `√π` and yields the rational identity
`(2n-1)‼ / 2ⁿ = (2n)! / (4ⁿ·n!)`; clearing denominators and casting back to `ℕ` gives
`(2n)! = (2n-1)‼·2ⁿ·n!`. Because the two Gamma forms are each obtained by an *independent*
telescoping of the half-integer recursion, the deduction is genuinely non-circular: the
combinatorial identity is recovered as the statement that the two telescopings agree.

## What is new

The double-factorial half-integer form is here proved standalone (the sibling instead
derived it *from* the central form *using* the very identity we now reprove). The
analytic → arithmetic lift `(2n)! = (2n-1)‼·2ⁿ·n!` obtained by equating two Gamma closed
forms is the new content; neither it nor the standalone induction is in Mathlib.

## Method

Induction for `gamma_nat_add_half_oddDF`: base `Γ(1/2)=√π`; step uses
`Γ((k+1)+1/2) = (k+1/2)·Γ(k+1/2)` and the odd-double-factorial recursion
`(2(k+1)-1)‼ = (2k+1)·(2k-1)‼` (`oddDoubleFactorial_succ`). Equating with the parent's
central form and clearing denominators over `ℝ` recovers the real identity
`((2n-1)‼ : ℝ)·2ⁿ·n! = (2n)!`; `Nat.cast_injective` lifts it to `ℕ`.

## References

* Mathlib: `Mathlib/Data/Nat/Factorial/DoubleFactorial.lean`,
  `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean`.
* Whittaker & Watson, *A Course of Modern Analysis*, §12.14 (half-integer values of `Γ`).
-/
import Mathlib
import Proofs.GammaReflectionFormulaOQ01OQ03

namespace GammaReflectionFormulaOQ01OQ03OQ01OQ01

open scoped Real Nat

/-! ## The odd double-factorial recursion -/

/-- **Odd double-factorial successor step.**
`(2(k+1)-1)‼ = (2k+1)·(2k-1)‼` for every `k : ℕ`. After rewriting `2(k+1)-1 = 2k+1` this
is exactly `Nat.doubleFactorial_add_one : (m+1)‼ = (m+1)·(m-1)‼` at `m = 2k`. -/
theorem oddDoubleFactorial_succ (k : ℕ) :
    (2 * (k + 1) - 1)‼ = (2 * k + 1) * (2 * k - 1)‼ := by
  have e1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  rw [e1, Nat.doubleFactorial_add_one]

/-! ## The standalone double-factorial half-integer Gamma value -/

/-- **Double-factorial closed form of `Γ` at half-integers, proved standalone.**
`Γ(n + 1/2) = (2n-1)‼ · √π / 2ⁿ` for every `n : ℕ`. Unlike the sibling
`GammaReflectionFormulaOQ01OQ03OQ01.gamma_nat_add_half_doubleFactorial`, this is obtained
*directly* by induction on the functional equation `Γ(s+1) = s·Γ(s)`, with no use of the
factorial identity `(2n)! = (2n-1)‼·2ⁿ·n!`. -/
theorem gamma_nat_add_half_oddDF (n : ℕ) :
    Real.Gamma (n + 1 / 2) = ((2 * n - 1)‼ : ℝ) * Real.sqrt π / 2 ^ n := by
  induction n with
  | zero =>
    -- `(2·0-1)‼ = 0‼ = 1`, `2⁰ = 1`: reduces to `Γ(1/2) = √π`.
    have h0 : (2 * 0 - 1)‼ = 1 := rfl
    simp only [Nat.cast_zero, zero_add, h0, Nat.cast_one, pow_zero, one_mul, div_one]
    exact Real.Gamma_one_half_eq
  | succ k ih =>
    have hs : ((k : ℝ) + 1 / 2) ≠ 0 := by positivity
    have h2 : (2 : ℝ) ^ k ≠ 0 := by positivity
    -- Step `Γ((k+1)+1/2) = (k+1/2)·Γ(k+1/2)`, substitute the IH.
    have harg : ((k + 1 : ℕ) : ℝ) + 1 / 2 = ((k : ℝ) + 1 / 2) + 1 := by push_cast; ring
    -- Odd double-factorial recursion, transported to `ℝ`.
    have hdf : (((2 * (k + 1) - 1)‼ : ℕ) : ℝ)
        = (2 * (k : ℝ) + 1) * (((2 * k - 1)‼ : ℕ) : ℝ) := by
      rw [oddDoubleFactorial_succ]; push_cast; ring
    rw [harg, Real.Gamma_add_one hs, ih, hdf, pow_succ]
    field_simp

/-! ## The analytic reproof of the factorial identity -/

/-- **Double-factorial form divided by `Γ(1/2) = √π`.**
`Γ(n+1/2)/√π = (2n-1)‼/2ⁿ`: the half-integer Gamma quotient as the odd double factorial
scaled by `2⁻ⁿ`. The `√π`-free shadow of `gamma_nat_add_half_oddDF`. -/
theorem gamma_nat_add_half_oddDF_div_sqrt_pi (n : ℕ) :
    Real.Gamma (n + 1 / 2) / Real.sqrt π = ((2 * n - 1)‼ : ℝ) / 2 ^ n := by
  rw [gamma_nat_add_half_oddDF]
  have hπ : Real.sqrt π ≠ 0 := by positivity
  field_simp

/-- **The factorial identity, recovered analytically over `ℝ`.**
Both `(2n-1)‼/2ⁿ` and `(2n)!/(4ⁿ·n!)` equal the `√π`-free quotient `Γ(n+1/2)/√π`, so they
are equal; cross-multiplying gives `((2n-1)‼ : ℝ)·2ⁿ·n! = (2n)!`. No appeal to the
combinatorial split. -/
theorem two_mul_factorial_eq_real (n : ℕ) :
    (((2 * n - 1)‼ : ℕ) : ℝ) * 2 ^ n * (n.factorial : ℝ) = ((2 * n).factorial : ℝ) := by
  -- The two rational quotients agree (both are `Γ(n+1/2)/√π`).
  have hrat : ((2 * n - 1)‼ : ℝ) / 2 ^ n
      = ((2 * n).factorial : ℝ) / (4 ^ n * (n.factorial : ℝ)) :=
    (gamma_nat_add_half_oddDF_div_sqrt_pi n).symm.trans
      (GammaReflectionFormulaOQ01OQ03.gamma_nat_add_half_div_sqrt_pi n)
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hfac : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hden : (4 : ℝ) ^ n * (n.factorial : ℝ) ≠ 0 := by positivity
  have h4 : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  -- Cross-multiply, expand `4ⁿ = 2ⁿ·2ⁿ`, then cancel one `2ⁿ`.
  rw [div_eq_div_iff h2 hden, h4] at hrat
  have key : ((((2 * n - 1)‼ : ℕ) : ℝ) * 2 ^ n * (n.factorial : ℝ)) * 2 ^ n
      = ((2 * n).factorial : ℝ) * 2 ^ n := by
    linear_combination hrat
  exact mul_right_cancel₀ h2 key

/-- **The factorial identity `(2n)! = (2n-1)‼·2ⁿ·n!`, proved analytically.**
The same statement as the sibling's combinatorial `two_mul_factorial_eq`, but obtained by
lifting the real identity `two_mul_factorial_eq_real` back to `ℕ` via injectivity of the
cast — an analytic proof of a combinatorial fact. -/
theorem two_mul_factorial_eq (n : ℕ) :
    (2 * n)! = (2 * n - 1)‼ * 2 ^ n * n ! := by
  have h := two_mul_factorial_eq_real n
  have hcast : (((2 * n - 1)‼ * 2 ^ n * n ! : ℕ) : ℝ) = ((2 * n)! : ℝ) := by
    push_cast; linarith [h]
  exact_mod_cast hcast.symm

/-! ## The Legendre-duplication route (the open question, verbatim)

The deduction above equated two closed forms of `Γ(n+1/2)`. The open question asks instead
for the route through **Legendre's duplication formula**
`Γ(s)·Γ(s+1/2) = Γ(2s)·2^(1-2s)·√π` (`Real.Gamma_mul_Gamma_add_half`). Evaluated at
`s = n+1/2` its three Gamma factors are all elementary —
`Γ(n+1/2) = (2n-1)‼·√π/2ⁿ` (the standalone form above), `Γ((n+1/2)+1/2) = Γ(n+1) = n!`,
and `Γ(2(n+1/2)) = Γ(2n+1) = (2n)!` — while `2^(1-2(n+1/2)) = 2^(-2n)`. Substituting and
cancelling the common `√π` recovers the *same* identity `(2n)! = (2n-1)‼·2ⁿ·n!`, now read
off the duplication formula directly. -/

/-- **The factorial identity, from the duplication formula at `s = n+1/2`.**
`((2n-1)‼ : ℝ)·2ⁿ·n! = (2n)!`, obtained by substituting the three elementary Gamma values
into `Real.Gamma_mul_Gamma_add_half (n+1/2)` and cancelling `√π`. Independent of the
two-closed-forms argument (`two_mul_factorial_eq_real`): here a *single* analytic identity,
Legendre duplication, carries the whole deduction. -/
theorem two_mul_factorial_eq_via_duplication (n : ℕ) :
    (((2 * n - 1)‼ : ℕ) : ℝ) * 2 ^ n * (n.factorial : ℝ) = ((2 * n).factorial : ℝ) := by
  have hπ : (0 : ℝ) < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hdup := Real.Gamma_mul_Gamma_add_half ((n : ℝ) + 1 / 2)
  rw [gamma_nat_add_half_oddDF n,
      show (1 : ℝ) - 2 * ((n : ℝ) + 1 / 2) = -((2 * n : ℕ) : ℝ) by push_cast; ring,
      show ((n : ℝ) + 1 / 2) + 1 / 2 = ((n : ℝ) + 1) by ring,
      show 2 * ((n : ℝ) + 1 / 2) = ((2 * n : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast,
      Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial] at hdup
  -- `hdup : (2n-1)‼·√π/2ⁿ · n! = (2n)! · (2^(2n))⁻¹ · √π`.
  have h22 : (2 : ℝ) ^ (2 * n) = 2 ^ n * 2 ^ n := by rw [two_mul, pow_add]
  rw [h22] at hdup
  -- Collect both sides as `(…)·√π` and cancel `√π`.
  have hcollect : (((2 * n - 1)‼ : ℝ) * (n.factorial : ℝ) / 2 ^ n) * Real.sqrt π
      = (((2 * n).factorial : ℝ) / (2 ^ n * 2 ^ n)) * Real.sqrt π := by
    rw [div_eq_mul_inv ((2 * n).factorial : ℝ)]; linear_combination hdup
  have hcancel := mul_right_cancel₀ (ne_of_gt hπ) hcollect
  rw [div_eq_div_iff h2 (by positivity)] at hcancel
  -- `hcancel : (2n-1)‼·n!·(2ⁿ·2ⁿ) = (2n)!·2ⁿ`; cancel one `2ⁿ`.
  have key : (((2 * n - 1)‼ : ℝ) * 2 ^ n * (n.factorial : ℝ)) * 2 ^ n
      = ((2 * n).factorial : ℝ) * 2 ^ n := by linear_combination hcancel
  exact mul_right_cancel₀ h2 key

/-! ## Consequences -/

/-- **The odd double factorial as a factorial quotient.**
`(2n-1)‼ = (2n)! / (2ⁿ·n!)`, the immediate divisibility consequence of the identity. -/
theorem oddDoubleFactorial_eq_factorial_div (n : ℕ) :
    (2 * n - 1)‼ = (2 * n)! / (2 ^ n * n !) := by
  have h := two_mul_factorial_eq n
  have hpos : 0 < 2 ^ n * n ! := Nat.mul_pos (pow_pos (by norm_num) n) (Nat.factorial_pos n)
  have h' : (2 * n)! = (2 * n - 1)‼ * (2 ^ n * n !) := by rw [h]; ring
  exact (Nat.div_eq_of_eq_mul_left hpos h').symm

/-- **Spot check `n = 3`.** `6! = 720 = 5‼ · 2³ · 3! = 15 · 8 · 6`. -/
theorem two_mul_factorial_eq_three : (6)! = (5)‼ * 2 ^ 3 * (3)! := by decide

end GammaReflectionFormulaOQ01OQ03OQ01OQ01
