/-
Erdős Problem #67: The Erdős Discrepancy Problem

If f: ℕ → {-1, +1}, then for every C > 0, do there exist d, m ≥ 1 such that
  |Σ_{k=1}^m f(kd)| > C?

**Status**: SOLVED by Terence Tao (2015)

**Answer**: YES. No matter how you assign ±1 to the natural numbers, the partial
sums along some arithmetic progression will eventually exceed any bound C.

This was a famous open problem for over 80 years. Tao's proof uses deep connections
to multiplicative number theory and the Elliott conjecture.

**Prize**: $500 (collected by Tao)

Reference: https://erdosproblems.com/67
Tao's paper: "The Erdős discrepancy problem" Discrete Analysis (2016)
-/

import Mathlib

open Finset
open scoped BigOperators

namespace Erdos67

/-!
## Background

The discrepancy of a sequence f: ℕ → {-1, +1} measures how "unbalanced" it can be
along arithmetic progressions. The sum Σ_{k=1}^m f(kd) counts how many more +1s
than -1s (or vice versa) appear among f(d), f(2d), ..., f(md).

Erdős asked whether this discrepancy must be unbounded for EVERY sequence f.
In other words, can you cleverly balance the ±1s to keep all arithmetic
progression sums bounded?

The answer is NO—no matter how clever you are, some progression will have
arbitrarily large discrepancy.
-/

/--
The **discrepancy** of a ±1 sequence f along the arithmetic progression
{d, 2d, ..., md} is the absolute value of the sum of f values.

This measures how unbalanced the sequence is on this progression.
-/
def discrepancy (f : ℕ → ℤ) (d m : ℕ) : ℤ :=
  |∑ k ∈ Icc 1 m, f (k * d)|

/--
A sequence has **bounded discrepancy** with bound C if all arithmetic
progression sums are at most C in absolute value.

Erdős asked whether bounded discrepancy sequences exist for large C.
-/
def hasBoundedDiscrepancy (f : ℕ → ℤ) (C : ℕ) : Prop :=
  ∀ d m : ℕ, d ≥ 1 → m ≥ 1 → discrepancy f d m ≤ C

/--
A function is a **±1 sequence** if it only takes values +1 and -1.
-/
def isPlusMinusOne (f : ℕ → ℤ) : Prop :=
  ∀ n : ℕ, f n = 1 ∨ f n = -1

/-!
## The Main Theorem (Tao 2015)

Terence Tao proved that NO ±1 sequence has bounded discrepancy.
Equivalently, for any ±1 sequence and any bound C, some arithmetic
progression has discrepancy exceeding C.
-/

/--
**The Erdős Discrepancy Theorem** (Tao 2015)

For any ±1 sequence f and any C > 0, there exist d, m ≥ 1 such that
the discrepancy along {d, 2d, ..., md} exceeds C.

This is stated as an axiom because Tao's proof is highly non-trivial,
using the theory of multiplicative functions and analytic number theory.
-/
axiom erdosDiscrepancy :
  ∀ (f : ℕ → ℤ), isPlusMinusOne f →
    ∀ C : ℕ, ∃ d m : ℕ, d ≥ 1 ∧ m ≥ 1 ∧ discrepancy f d m > C

/--
Equivalent formulation: No ±1 sequence has bounded discrepancy.
-/
theorem noBoundedDiscrepancy :
    ∀ (f : ℕ → ℤ), isPlusMinusOne f → ∀ C : ℕ, ¬hasBoundedDiscrepancy f C := by
  intro f hf C hBound
  obtain ⟨d, m, hd, hm, hDisc⟩ := erdosDiscrepancy f hf C
  have := hBound d m hd hm
  omega

/-!
## The Complex Variant

Tao also proved a more general version where f takes values on the
unit circle in ℂ (not just ±1). The discrepancy still must be unbounded.
-/

/--
Complex discrepancy: the norm of the sum of f values on an arithmetic progression.
-/
noncomputable def complexDiscrepancy (f : ℕ → ℂ) (d m : ℕ) : ℝ :=
  ‖∑ k ∈ Icc 1 m, f (k * d)‖

/--
A function maps to the **unit circle** if all values have norm 1.
-/
def mapsToUnitCircle (f : ℕ → ℂ) : Prop :=
  ∀ n : ℕ, ‖f n‖ = 1

/--
**The Erdős Discrepancy Theorem (Complex Version)** (Tao 2015)

For any sequence f: ℕ → S¹ (unit circle) and any C > 0, there exist
d, m ≥ 1 such that the complex discrepancy exceeds C.

This is strictly stronger than the ±1 version, since {-1, +1} ⊂ S¹.
-/
axiom erdosDiscrepancyComplex :
  ∀ (f : ℕ → ℂ), mapsToUnitCircle f →
    ∀ C : ℝ, C > 0 → ∃ d m : ℕ, d ≥ 1 ∧ m ≥ 1 ∧ complexDiscrepancy f d m > C

/-!
## Erdős's Stronger Conjecture

Erdős conjectured an even stronger statement: not only is the discrepancy
unbounded, but it grows at least logarithmically in x.

This stronger conjecture remains OPEN.
-/

/--
**Erdős's Stronger Conjecture** (OPEN)

Erdős conjectured that
  max_{md ≤ x} |Σ_{k=1}^m f(kd)| ≫ log x

In other words, the discrepancy should grow at least logarithmically.
We state this without asserting its truth.
-/
def ErdosStrongerConjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ (f : ℕ → ℤ), isPlusMinusOne f →
    ∀ x : ℕ, x ≥ 2 →
      ∃ d m : ℕ, d ≥ 1 ∧ m ≥ 1 ∧ m * d ≤ x ∧
        discrepancy f d m > c * Real.log x

/-!
## The Multiplicative Case

Erdős also asked about the special case when f is completely multiplicative
(f(mn) = f(m)f(n)). This case is easier and was known before Tao's result.
-/

/--
A function is **completely multiplicative** if f(mn) = f(m)f(n) for all m, n.
-/
def isCompletelyMultiplicative (f : ℕ → ℤ) : Prop :=
  ∀ m n : ℕ, f (m * n) = f m * f n

/--
For completely multiplicative ±1 functions, the discrepancy is known to be
unbounded. This was proved before Tao's general result.
-/
axiom multiplicativeDiscrepancy :
  ∀ (f : ℕ → ℤ), isPlusMinusOne f → isCompletelyMultiplicative f →
    ∀ C : ℕ, ∃ d m : ℕ, d ≥ 1 ∧ m ≥ 1 ∧ discrepancy f d m > C

/-!
## Historical Notes

The Erdős Discrepancy Problem was posed in the 1930s and remained open for
over 80 years. In 2010, the Polymath5 project attempted a collaborative attack
but did not succeed. In 2015, Terence Tao announced a solution using a
novel connection to the Elliott conjecture in analytic number theory.

Key steps in Tao's proof:
1. Reduce to the case of multiplicative functions
2. Use a logarithmic averaging argument
3. Apply a special case of the Elliott conjecture
4. Show that no completely multiplicative function on primes avoids large sums
-/

/-- The main result implies that discrepancy 2 sequences don't exist. -/
theorem no_discrepancy_2_sequence :
    ¬∃ (f : ℕ → ℤ), isPlusMinusOne f ∧ hasBoundedDiscrepancy f 2 := by
  intro ⟨f, hf, hBound⟩
  exact noBoundedDiscrepancy f hf 2 hBound

end Erdos67
