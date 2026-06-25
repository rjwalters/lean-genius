/-
# Möbius Inversion of the Totient: φ = μ ∗ id

## What This Proves
The **Möbius-inversion formula for Euler's totient**: for every `n`,

  φ(n)  =  Σ_{d | n} μ(d) · (n / d),

equivalently in `divisorsAntidiagonal` shape,

  φ(n)  =  Σ_{(a,b) ∈ antidiagonal n} μ(a) · b,

i.e. the totient is the Dirichlet convolution `μ ∗ id` of the Möbius
function with the identity function (working over `ℤ`, since
`ArithmeticFunction.moebius` is `ℤ`-valued).

## Where this sits in the convolution triangle
The parent entry `euler-totient-oq-04` proves the **forward** Gauss
divisor-sum identity `n = Σ_{d|n} φ(d)`, i.e. `φ ∗ ζ = id`. The sibling
`euler-totient-oq-04-oq-01` proves the **kernel** identity
`Σ_{d|n} μ(d) = [n = 1]`, i.e. `μ ∗ ζ = ε`. This leaf is the **inverse**
of the parent: it solves the Gauss identity for `φ` by Möbius inversion,
closing the triangle

    φ ∗ ζ = id ,   μ ∗ ζ = ε     ⟹     φ = id ∗ μ = μ ∗ id .

## Proof
Mathlib supplies the abstract inversion `sum_eq_iff_sum_mul_moebius_eq`:
for `f g : ℕ → ℤ`,

  (∀ n>0, Σ_{i|n} f i = g n)  ↔  (∀ n>0, Σ_{(a,b)} μ(a)·g(b) = f n).

We instantiate `f = φ` (cast to `ℤ`) and `g = id`. The left-hand side is
exactly Gauss's identity `Nat.sum_totient`, so the right-hand side gives
the antidiagonal form for free. We then fold the antidiagonal back to a
divisor sum with `Nat.sum_divisorsAntidiagonal`, and patch the `n = 0`
edge case (where both sides are `0`).

## Why this isn't just a Mathlib wrapper
Mathlib stores the *generic* Möbius-inversion machine and `Nat.sum_totient`
separately, but exposes **no** statement of `φ = μ ∗ id` — neither the
pointwise signed divisor sum nor the antidiagonal convolution. This file
supplies that named bridge, the dual of the parent's Gauss identity.

## Status
**Verified** — main theorem `totient_eq_sum_moebius` fully proved.
Zero `sorry`s, zero `axiom`s.

## Mathlib Dependencies
- `Nat.sum_totient` : `Σ_{d|n} φ(d) = n`  (Gauss forward identity)
- `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq` : Möbius inversion
- `Nat.sum_divisorsAntidiagonal` : antidiagonal ↔ divisor-sum folding
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Totient

open Nat ArithmeticFunction
open scoped BigOperators ArithmeticFunction.Moebius

namespace EulerTotientOQ04OQ02

/-- The Gauss divisor-sum identity, cast to `ℤ`: `Σ_{d|n} φ(d) = n`.
This is the hypothesis side of Möbius inversion. -/
theorem sum_totient_int (n : ℕ) :
    ∑ d ∈ n.divisors, (φ d : ℤ) = (n : ℤ) := by
  exact_mod_cast Nat.sum_totient n

/-- **Möbius inversion of the totient (antidiagonal form).**
For `n > 0`, `φ(n) = Σ_{(a,b) ∈ antidiagonal n} μ(a) · b`. This is the
Dirichlet convolution `(μ ∗ id)(n)` written out over the antidiagonal. -/
theorem totient_eq_sum_antidiagonal (n : ℕ) (hn : 0 < n) :
    (φ n : ℤ) = ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℤ) * (x.2 : ℤ) := by
  have h :=
    (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℤ)
        (f := fun d => (φ d : ℤ)) (g := fun n => (n : ℤ))).mp
      (fun m _ => sum_totient_int m) n hn
  exact h.symm

/-- **Möbius inversion of the totient (divisor-sum form).**
For every `n`, `φ(n) = Σ_{d|n} μ(d) · (n / d)`. Equivalently
`φ = μ ∗ id`, the inverse of Gauss's identity `n = Σ_{d|n} φ(d)`.

Holds for `n = 0` as well: both sides are `0` (the empty divisor sum). -/
theorem totient_eq_sum_moebius (n : ℕ) :
    (φ n : ℤ) = ∑ d ∈ n.divisors, (μ d : ℤ) * ((n / d : ℕ) : ℤ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [totient_eq_sum_antidiagonal n hn,
      Nat.sum_divisorsAntidiagonal (fun i j => (μ i : ℤ) * (j : ℤ))]

/-- Symmetric divisor-sum form using the `n/d ↔ d` reflection:
`φ(n) = Σ_{d|n} μ(n/d) · d`. -/
theorem totient_eq_sum_moebius_swap (n : ℕ) (hn : 0 < n) :
    (φ n : ℤ) = ∑ d ∈ n.divisors, (μ (n / d) : ℤ) * (d : ℤ) := by
  rw [totient_eq_sum_antidiagonal n hn,
    Nat.sum_divisorsAntidiagonal' (fun i j => (μ i : ℤ) * (j : ℤ))]

end EulerTotientOQ04OQ02
