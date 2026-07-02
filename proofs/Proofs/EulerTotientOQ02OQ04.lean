/-
# Characterizing the Totient: the Gauss Divisor-Sum Determines φ Uniquely

## What This Proves
Euler's totient satisfies two structural properties:

  * **Gauss's divisor-sum identity**:  `Σ_{d | n} φ(d) = n`   (i.e. `φ ∗ ζ = id`);
  * **multiplicativity**:  `φ(mn) = φ(m)·φ(n)` for `gcd(m,n) = 1`.

The open question asks how these two properties *together* characterize φ among all
multiplicative arithmetic functions. The answer is sharp, and stronger than the question:

  **the divisor-sum identity ALONE pins the function down.**

Any function `f : ℕ → ℤ` with `Σ_{d | n} f(d) = n` for all `n > 0` must equal `φ` on the
positive integers — multiplicativity is not even needed for uniqueness. Consequently φ is the
UNIQUE multiplicative function satisfying Gauss's identity, and it is *a fortiori* the unique
function of any kind satisfying it.

## Where this sits
The sibling `euler-totient-oq-04-oq-02` proves the inversion `φ = μ ∗ id` (solving Gauss's
identity FOR φ). This leaf proves the dual *uniqueness*: the identity has only one solution,
so it characterizes φ. Both rest on the invertibility of `ζ` in the Dirichlet ring
(`μ ∗ ζ = ε`), packaged by Mathlib as Möbius inversion.

## Proof
`ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq` says, for `f g : ℕ → ℤ`,

    (∀ n>0, Σ_{d|n} f d = g n)  ↔  (∀ n>0, Σ_{(a,b)} μ(a)·g(b) = f n).

Instantiate `g = id`. Both `f` (by hypothesis) and `φ` (by Gauss's identity `Nat.sum_totient`)
have the same divisor-sum `g = id`, so the RIGHT-hand side — a single expression depending only
on `g` — equals both `f n` and `φ n`. Hence `f n = φ n` for `n > 0`.

## Why this isn't just a Mathlib wrapper
Mathlib has the abstract inversion machine and `Nat.sum_totient`, but no statement that the
Gauss identity *characterizes* φ. This file supplies that uniqueness theorem, its multiplicative
corollary (the exact form the open question asks for), and the witness that φ satisfies both
properties — so the characterization is non-vacuous.

## Status
**Verified** — zero `sorry`, zero `axiom` (only propext / Classical.choice / Quot.sound).

## Mathlib Dependencies
- `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq` : Möbius inversion over a ring
- `Nat.sum_totient` : `Σ_{d|n} φ(d) = n`
- `Nat.totient_mul` : multiplicativity of φ on coprime arguments
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Totient

open Nat ArithmeticFunction
open scoped BigOperators ArithmeticFunction.Moebius

namespace EulerTotientOQ02OQ04

/-- Gauss's divisor-sum identity for φ, cast to `ℤ`: `Σ_{d | n} φ(d) = n`.
This is the property whose *uniqueness* we establish. -/
theorem totient_sum_eq (n : ℕ) :
    ∑ d ∈ n.divisors, (φ d : ℤ) = (n : ℤ) := by
  exact_mod_cast Nat.sum_totient n

/-- φ is multiplicative: `φ(m·n) = φ(m)·φ(n)` for coprime `m, n`.
The second of the two characterizing properties. -/
theorem totient_multiplicative {m n : ℕ} (h : m.Coprime n) :
    φ (m * n) = φ m * φ n :=
  Nat.totient_mul h

/-- **Uniqueness of the Gauss divisor-sum identity.**
If `f : ℕ → ℤ` satisfies `Σ_{d | n} f(d) = n` for every `n > 0`, then `f` agrees with the
totient on the positive integers. The divisor-sum identity has a *single* solution — φ —
so it characterizes the totient with no further hypotheses (multiplicativity is not needed). -/
theorem eq_totient_of_sum_eq (f : ℕ → ℤ)
    (hf : ∀ n : ℕ, 0 < n → ∑ d ∈ n.divisors, f d = (n : ℤ)) :
    ∀ n > 0, f n = (φ n : ℤ) := by
  -- Both `f` and `d ↦ φ d` have the same divisor-sum `g = id`, so Möbius inversion
  -- forces them to share the same inverse expression, hence to be equal on `n > 0`.
  have key_f :=
    (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℤ)
      (f := f) (g := fun n => (n : ℤ))).mp hf
  have key_φ :=
    (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℤ)
      (f := fun d => (φ d : ℤ)) (g := fun n => (n : ℤ))).mp
      (fun m _ => totient_sum_eq m)
  intro n hn
  exact (key_f n hn).symm.trans (key_φ n hn)

/-- **Characterization among multiplicative functions (the open question's form).**
φ is the unique multiplicative function satisfying Gauss's divisor-sum identity:
if `f` is multiplicative (in the sense `f(1) = 1` and `f(m·n) = f(m)·f(n)` for coprime `m, n`)
and `Σ_{d | n} f(d) = n` for all `n > 0`, then `f = φ` on the positive integers. The
multiplicativity hypothesis is displayed for faithfulness to the question, but is redundant:
`eq_totient_of_sum_eq` already gives the conclusion from the divisor-sum alone. -/
theorem eq_totient_of_multiplicative_of_sum_eq (f : ℕ → ℤ)
    (_hmul : f 1 = 1 ∧ ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n)
    (hf : ∀ n : ℕ, 0 < n → ∑ d ∈ n.divisors, f d = (n : ℤ)) :
    ∀ n > 0, f n = (φ n : ℤ) :=
  eq_totient_of_sum_eq f hf

/-- **The two properties together are realized by φ and by nothing else.**
For any `f : ℕ → ℤ`, `f` agrees with φ on the positive integers **iff** it satisfies Gauss's
divisor-sum identity there. This is the precise sense in which the divisor-sum identity
characterizes the totient: the solution set of the identity is exactly `{φ}`. -/
theorem sum_eq_iff_eq_totient (f : ℕ → ℤ) :
    (∀ n : ℕ, 0 < n → ∑ d ∈ n.divisors, f d = (n : ℤ)) ↔ (∀ n > 0, f n = (φ n : ℤ)) := by
  constructor
  · exact eq_totient_of_sum_eq f
  · intro hfφ n hn
    calc ∑ d ∈ n.divisors, f d
        = ∑ d ∈ n.divisors, (φ d : ℤ) :=
          Finset.sum_congr rfl fun d hd => hfφ d (Nat.pos_of_mem_divisors hd)
      _ = (n : ℤ) := totient_sum_eq n

#check @eq_totient_of_sum_eq
#check @eq_totient_of_multiplicative_of_sum_eq
#check @sum_eq_iff_eq_totient

end EulerTotientOQ02OQ04
