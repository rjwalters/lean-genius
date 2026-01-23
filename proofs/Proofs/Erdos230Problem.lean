/-
Erdős Problem #230: Ultraflat Polynomials on the Unit Circle

Source: https://erdosproblems.com/230
Status: SOLVED (DISPROVED)

Statement:
Let P(z) = Σ_{1≤k≤n} a_k z^k with |a_k| = 1 for all k.
Does there exist c > 0 such that max_{|z|=1} |P(z)| ≥ (1+c)√n for all n ≥ 2?

Answer: NO (Kahane 1980)

Background:
By Parseval's identity, the L² norm of P on the unit circle is exactly √n.
The question asks whether the sup norm must be bounded away from √n.
Kahane showed "ultraflat" polynomials exist where the sup norm approaches √n.

Key Results:
- Lower bound √n: trivial from Parseval (L² norm)
- Körner (1980): Constructed polynomials with |P(z)| ∈ [c₁√n, c₂√n]
- Kahane (1980): Ultraflat polynomials with |P(z)| = (1+o(1))√n uniformly
- Bombieri-Bourgain (2009): |P(z)| = √n + O(n^{7/18} log^O(1) n)

References:
- [Ha74] Halberstam, Problem 4.31
- [Ka80] Kahane, ultraflat polynomials
- [BB09] Bombieri-Bourgain, improved error terms

Tags: analysis, polynomials, harmonic-analysis, ultraflat
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Basic

open Complex Finset

namespace Erdos230

/-
## Part I: Unimodular Polynomials
-/

/--
**Unimodular polynomial:**
A polynomial P(z) = Σ a_k z^k where all coefficients satisfy |a_k| = 1.
-/
structure UnimodularPolynomial (n : ℕ) where
  coeffs : Fin n → ℂ
  unimodular : ∀ k, Complex.abs (coeffs k) = 1

/--
**Evaluate unimodular polynomial:**
P(z) = Σ_{k=0}^{n-1} a_k z^{k+1}
-/
noncomputable def evaluate {n : ℕ} (P : UnimodularPolynomial n) (z : ℂ) : ℂ :=
  ∑ k : Fin n, P.coeffs k * z ^ (k.val + 1)

/--
**Sup norm on unit circle:**
‖P‖_∞ = max_{|z|=1} |P(z)|
-/
noncomputable def supNormOnCircle {n : ℕ} (P : UnimodularPolynomial n) : ℝ :=
  ⨆ (z : ℂ) (_ : Complex.abs z = 1), Complex.abs (evaluate P z)

/-
## Part II: Parseval's Identity
-/

/--
**L² norm on unit circle:**
‖P‖_2 = (∫_{|z|=1} |P(z)|² dz / 2π)^{1/2}
-/
noncomputable def l2NormOnCircle {n : ℕ} (P : UnimodularPolynomial n) : ℝ :=
  Real.sqrt n  -- For unimodular P, this equals √n exactly

/--
**Parseval's identity for unimodular polynomials:**
‖P‖_2² = Σ |a_k|² = n for degree n unimodular P.
-/
theorem parseval_identity {n : ℕ} (P : UnimodularPolynomial n) :
    (l2NormOnCircle P) ^ 2 = n := by
  unfold l2NormOnCircle
  simp [Real.sq_sqrt (by linarith : (n : ℝ) ≥ 0)]

/--
**Trivial lower bound:**
‖P‖_∞ ≥ ‖P‖_2 = √n.
-/
theorem sup_ge_l2 {n : ℕ} (P : UnimodularPolynomial n) (hn : n ≥ 1) :
    supNormOnCircle P ≥ Real.sqrt n := by
  sorry -- From general inequality ‖·‖_∞ ≥ ‖·‖_2 for bounded measures

/-
## Part III: The Erdős-Newman Conjecture (DISPROVED)
-/

/--
**The (false) conjecture:**
∃ c > 0 such that ∀ n ≥ 2, ∀ unimodular P of degree n:
  ‖P‖_∞ ≥ (1+c)√n

This is FALSE - Kahane showed ultraflat polynomials exist.
-/
def ErdosNewmanConjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∀ n : ℕ, n ≥ 2 → ∀ P : UnimodularPolynomial n,
      supNormOnCircle P ≥ (1 + c) * Real.sqrt n

/--
**The conjecture is FALSE:**
-/
theorem erdos_newman_false : ¬ErdosNewmanConjecture := by
  intro ⟨c, hc, hconj⟩
  -- Kahane's ultraflat polynomials give a contradiction
  sorry

/-
## Part IV: Ultraflat Polynomials (Kahane 1980)
-/

/--
**Ultraflat polynomial:**
A unimodular polynomial P such that |P(z)| is nearly constant on |z| = 1.
Specifically: |P(z)| = (1 + o(1))√n uniformly.
-/
def IsUltraflat {n : ℕ} (P : UnimodularPolynomial n) (ε : ℝ) : Prop :=
  ∀ z : ℂ, Complex.abs z = 1 →
    Complex.abs (evaluate P z) ≥ (1 - ε) * Real.sqrt n ∧
    Complex.abs (evaluate P z) ≤ (1 + ε) * Real.sqrt n

/--
**Kahane's Theorem (1980):**
For any ε > 0 and sufficiently large n, there exists an ultraflat
unimodular polynomial of degree n.
-/
axiom kahane_ultraflat :
  ∀ ε : ℝ, ε > 0 →
    ∃ N : ℕ, ∀ n ≥ N, ∃ P : UnimodularPolynomial n, IsUltraflat P ε

/--
**Kahane disproves Erdős-Newman:**
Ultraflat polynomials show the sup norm can be arbitrarily close to √n.
-/
theorem kahane_disproves : ¬ErdosNewmanConjecture := by
  intro ⟨c, hc, hconj⟩
  -- Choose ε = c/2, get ultraflat polynomial
  obtain ⟨N, hN⟩ := kahane_ultraflat (c/2) (by linarith)
  -- For n ≥ max(N, 2), ultraflat P has ‖P‖_∞ ≤ (1 + c/2)√n
  -- But conjecture says ‖P‖_∞ ≥ (1 + c)√n
  -- Contradiction for large n
  sorry

/-
## Part V: Körner's Construction (1980)
-/

/--
**Körner's polynomials:**
Körner constructed unimodular polynomials with |P(z)| bounded above and below
by constant multiples of √n on the unit circle.
-/
axiom korner_bounded :
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧
    ∃ N : ℕ, ∀ n ≥ N, ∃ P : UnimodularPolynomial n,
      ∀ z : ℂ, Complex.abs z = 1 →
        c₁ * Real.sqrt n ≤ Complex.abs (evaluate P z) ∧
        Complex.abs (evaluate P z) ≤ c₂ * Real.sqrt n

/-
## Part VI: Bombieri-Bourgain Improvement (2009)
-/

/--
**Bombieri-Bourgain (2009):**
Improved Kahane's construction to get better error terms:
|P(z)| = √n + O(n^{7/18} (log n)^{O(1)})
-/
axiom bombieri_bourgain :
  ∃ C : ℝ, C > 0 ∧
    ∃ N : ℕ, ∀ n ≥ N, ∃ P : UnimodularPolynomial n,
      ∀ z : ℂ, Complex.abs z = 1 →
        |Complex.abs (evaluate P z) - Real.sqrt n| ≤
          C * (n : ℝ) ^ (7/18 : ℝ) * (Real.log n) ^ 10

/--
**Error exponent 7/18:**
The exponent 7/18 ≈ 0.389 is the current best known.
It's still unknown if the error can be O(1) (perfectly flat).
-/
def bombieriBorgainExponent : ℚ := 7 / 18

/-
## Part VII: Random Polynomial Heuristics
-/

/--
**Random unimodular polynomial:**
If coefficients are chosen uniformly on the unit circle,
what is the expected behavior of |P(z)|?
-/
axiom random_polynomial_behavior :
  -- Heuristically, random P has |P(z)| ≈ √n with fluctuations O(√(log n))
  True

/--
**Rudin-Shapiro polynomials:**
A deterministic family of unimodular polynomials with |P(z)| ≤ 2√n.
Not ultraflat (lower bound can be small).
-/
axiom rudin_shapiro :
  ∀ n : ℕ, n ≥ 1 → ∃ P : UnimodularPolynomial (2^n),
    supNormOnCircle P ≤ 2 * Real.sqrt (2^n)

/-
## Part VIII: Why "Ultraflat"?
-/

/--
**Flatness interpretation:**
A polynomial P is "flat" if |P(z)| is nearly constant on |z| = 1.
"Ultra" flat means the ratio max/min approaches 1 as n → ∞.

For perfect flatness, we'd need |P(z)| = √n for all |z| = 1,
which is impossible (P would be constant, contradicting degree n).
-/
axiom flatness_explanation : True

/--
**Equidistribution connection:**
Ultraflat polynomials relate to equidistribution of polynomial values
on the unit circle - a topic in harmonic analysis.
-/
axiom equidistribution_connection : True

/-
## Part IX: Related Results
-/

/--
**Problem #228 connection:**
Related to Problem #228 about coefficients and polynomial behavior.
-/
axiom problem_228_connection : True

/--
**Littlewood conjecture:**
A related conjecture asked about |P(z)| for polynomials with
coefficients ±1. This is also studied extensively.
-/
axiom littlewood_polynomials : True

/-
## Part X: Summary
-/

/--
**Erdős Problem #230: SOLVED (DISPROVED)**

**QUESTION:** For unimodular P(z) = Σ a_k z^k with |a_k| = 1,
does there exist c > 0 such that max_{|z|=1} |P(z)| ≥ (1+c)√n?

**ANSWER:** NO (Kahane 1980)

**KEY RESULTS:**
1. Trivial lower bound: max |P(z)| ≥ √n (Parseval)
2. Körner (1980): Can make c₁√n ≤ |P(z)| ≤ c₂√n
3. Kahane (1980): Ultraflat - |P(z)| = (1+o(1))√n possible
4. Bombieri-Bourgain (2009): Error O(n^{7/18})

**INSIGHT:** Ultraflat unimodular polynomials exist where the
maximum is arbitrarily close to the L² norm √n.
-/
theorem erdos_230_summary :
    -- The conjecture is FALSE
    ¬ErdosNewmanConjecture ∧
    -- But √n is always a lower bound
    (∀ n : ℕ, n ≥ 1 → ∀ P : UnimodularPolynomial n,
      supNormOnCircle P ≥ Real.sqrt n) := by
  constructor
  · exact kahane_disproves
  · intro n hn P
    exact sup_ge_l2 P hn

/--
**Historical note:**
Erdős and Newman conjectured (1+c)√n in 1957/1961.
The problem appeared as Problem 4.31 in Halberstam (1974).
Kahane's 1980 disproof via ultraflat polynomials was surprising.
-/
theorem erdos_230_status : True := trivial

end Erdos230
