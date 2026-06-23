import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-!
# angle-trisection-cos-20-gal OQ-02: the algebraic core of `[ℚ(cos 2π/n) : ℚ] = φ(n)/2`

The parent entry (`angle-trisection-cos-20-gal`) computes `|Gal| = 3` for the minimal
polynomial of `cos 20° = cos(2π/18)`-type angles, and lists as an open question:

> *Is there a Mathlib path to the Kronecker–Weber theorem that would let one classify all
> abelian extensions of ℚ and prove `[ℚ(cos 2π/n) : ℚ] = φ(n)/2` for all `n ≥ 3`?*

Mathlib has neither Kronecker–Weber nor the degree of the maximal real subfield of a
cyclotomic field, so the *exact* field-degree formula is out of reach today. This file
supplies the **two algebraic facts that the formula rests on**, both fully proved with
`0` axioms:

1. **Where the `÷2` comes from.** Writing `ζ = e^{iθ}`, the value `2cos θ = ζ + ζ⁻¹`
   makes `ζ` a root of the *real* quadratic `X² − (2cos θ)X + 1`. So `ℚ(ζ)` is at most a
   degree-`2` extension of `ℚ(cos θ)`; against `[ℚ(ζ_n):ℚ] = φ(n)` (already in Mathlib)
   this is exactly the source of the halving `φ(n)/2`.

2. **An explicit algebraic witness for `cos 2π/n`.** Via Chebyshev polynomials,
   `T_n(cos 2π/n) = cos(2π) = 1`, so `cos 2π/n` is a root of `T_n − 1`.

We also record the consistency of `φ(n)/2` with the gallery's concrete results
(`cos 2π/7`, `cos 40° = cos 2π/9` both give degree `3 = φ(7)/2 = φ(9)/2`).

## Main results

* `two_cos_eq_exp_add_inv` : `2cos x = e^{ix} + e^{−ix}` over ℂ.
* `zeta_quadratic` : `ζ² − (2cos x)·ζ + 1 = 0` for `ζ = e^{ix}` — the index-`2` relation.
* `cos_chebyshev_eval` / `cos_two_pi_div_chebyshev_root` : `cos 2π/n` is a root of `Tₙ − 1`.
* `totient_div_two_cos_*` : `φ(n)/2` agrees with the gallery's computed degrees.
-/

namespace AngleTrisectionCos20GalOQ02

open Complex Polynomial

/-- **`2cos x = e^{ix} + e^{−ix}`** over `ℂ` (restating `Complex.two_cos`). The real and
    imaginary exponentials average to the cosine; this is the bridge from the trigonometric
    value `cos x` to the root of unity `ζ = e^{ix}`. -/
theorem two_cos_eq_exp_add_inv (x : ℂ) :
    2 * Complex.cos x = Complex.exp (x * I) + Complex.exp (-x * I) :=
  Complex.two_cos x

/-- **The index-2 relation.** For `ζ = e^{ix}`, the root of unity satisfies the *real*
    quadratic `ζ² − (2cos x)·ζ + 1 = 0`. Equivalently `ζ` is a root of
    `X² − (2cos x)X + 1 ∈ ℝ(cos x)[X]`, so `[ℚ(ζ) : ℚ(cos x)] ≤ 2`. Combined with the
    cyclotomic degree `[ℚ(ζ_n):ℚ] = φ(n)`, this is precisely why `[ℚ(cos 2π/n):ℚ] = φ(n)/2`. -/
theorem zeta_quadratic (x : ℂ) :
    Complex.exp (x * I) ^ 2 - (2 * Complex.cos x) * Complex.exp (x * I) + 1 = 0 := by
  have hab : Complex.exp (x * I) * Complex.exp (-x * I) = 1 := by
    rw [← Complex.exp_add]
    rw [show x * I + -x * I = 0 by ring, Complex.exp_zero]
  rw [two_cos_eq_exp_add_inv]
  linear_combination -hab

/-- The same quadratic, phrased over a real angle `θ`: `ζ = e^{iθ}` is a root of
    `X² − (2·Real.cos θ)·X + 1`. -/
theorem zeta_quadratic_real (θ : ℝ) :
    Complex.exp (θ * I) ^ 2 - (2 * (Real.cos θ : ℂ)) * Complex.exp (θ * I) + 1 = 0 := by
  have := zeta_quadratic (θ : ℂ)
  rwa [← Complex.ofReal_cos] at this

/-- **Chebyshev evaluation** (restating `Polynomial.Chebyshev.T_real_cos`): the `n`-th
    Chebyshev polynomial of the first kind sends `cos θ` to `cos(nθ)`. -/
theorem cos_chebyshev_eval (n : ℤ) (θ : ℝ) :
    (Polynomial.Chebyshev.T ℝ n).eval (Real.cos θ) = Real.cos (n * θ) :=
  Polynomial.Chebyshev.T_real_cos θ n

/-- **An explicit algebraic witness for `cos 2π/n`.** Since `Tₙ(cos 2π/n) = cos(2π) = 1`,
    the number `cos 2π/n` is a root of `Tₙ − 1`. This is the concrete polynomial whose
    (irreducible) factors carry the minimal polynomial of degree `φ(n)/2`. -/
theorem cos_two_pi_div_chebyshev_root (n : ℕ) (hn : n ≠ 0) :
    (Polynomial.Chebyshev.T ℝ n).eval (Real.cos (2 * Real.pi / n)) = 1 := by
  rw [cos_chebyshev_eval]
  have hcast : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [show ((n : ℤ) : ℝ) * (2 * Real.pi / n) = 2 * Real.pi by push_cast; field_simp]
  exact Real.cos_two_pi

-- ============================================================
-- Consistency of φ(n)/2 with the gallery's concrete degrees
-- ============================================================

/-- `cos 2π/7` (regular heptagon): `φ(7)/2 = 3`, matching the gallery's cubic minimal
    polynomial with `|Gal| = 3`. -/
theorem totient_div_two_seven : Nat.totient 7 / 2 = 3 := by decide

/-- `cos 40° = cos 2π/9` (the `cos 20°` trisection sibling): `φ(9)/2 = 3`, again a cubic. -/
theorem totient_div_two_nine : Nat.totient 9 / 2 = 3 := by decide

/-- `cos 2π/5` (regular pentagon): `φ(5)/2 = 2`, a quadratic — `cos 36°` is constructible. -/
theorem totient_div_two_five : Nat.totient 5 / 2 = 2 := by decide

/-- `cos 2π/15`: `φ(15)/2 = 4`. A non-prime example where the formula gives a quartic. -/
theorem totient_div_two_fifteen : Nat.totient 15 / 2 = 4 := by decide

/-- For an odd prime `p`, the predicted degree `φ(p)/2 = (p−1)/2`. For `p = 7` this is `3`,
    the cubic responsible for the impossibility of trisecting `120° = 3 · 40°`. -/
theorem totient_div_two_odd_prime (p : ℕ) (hp : p.Prime) (_hodd : Odd p) :
    Nat.totient p / 2 = (p - 1) / 2 := by
  rw [Nat.totient_prime hp]

end AngleTrisectionCos20GalOQ02
