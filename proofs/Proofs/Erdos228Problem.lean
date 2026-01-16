/-
  Erdős Problem #228: Littlewood Conjecture on Flat Polynomials

  Source: https://erdosproblems.com/228
  Status: SOLVED (Balister-Bollobás-Morris-Sahasrabudhe-Tiba 2019)

  Question:
  Does there exist, for all large n, a polynomial P of degree n, with
  coefficients ±1, such that √n ≪ |P(z)| ≪ √n for all |z| = 1?

  Answer: YES

  This was originally conjectured by J.E. Littlewood. The existence of such
  "flat" Littlewood polynomials was proved by Balister, Bollobás, Morris,
  Sahasrabudhe, and Tiba in their landmark 2019 paper.

  A Littlewood polynomial is a polynomial with all coefficients ±1.
  A "flat" Littlewood polynomial has magnitude approximately √n everywhere
  on the unit circle, matching the average behavior of random ±1 sums.

  Reference:
  - Balister, Bollobás, Morris, Sahasrabudhe, Tiba, "Flat Littlewood
    Polynomials Exist", Annals of Mathematics 192 (2020), 977-1004.
  - Guy, "Unsolved Problems in Number Theory"
-/

import Mathlib

open Complex Polynomial Filter

namespace Erdos228

/-! ## Core Definitions -/

/-- A **Littlewood polynomial** has all coefficients in {-1, +1}. -/
def IsLittlewoodPolynomial (p : Polynomial ℂ) : Prop :=
  ∀ i ≤ p.natDegree, p.coeff i = 1 ∨ p.coeff i = -1

/-- A polynomial is **flat** on the unit circle if |P(z)| ∼ √(deg P)
    for all |z| = 1, i.e., bounded between c₁√n and c₂√n for constants
    c₁, c₂ > 0 independent of z and the degree. -/
def IsFlatOnUnitCircle (p : Polynomial ℂ) (c₁ c₂ : ℝ) : Prop :=
  let n := p.natDegree
  c₁ > 0 ∧ c₂ > 0 ∧
  ∀ z : ℂ, ‖z‖ = 1 → c₁ * Real.sqrt n ≤ ‖p.eval z‖ ∧ ‖p.eval z‖ ≤ c₂ * Real.sqrt n

/-! ## Littlewood's Problem -/

/--
**Erdős Problem #228** (originally Littlewood's conjecture):

For all sufficiently large n, does there exist a polynomial P of degree n
with coefficients ±1 such that √n ≪ |P(z)| ≪ √n for all |z| = 1?

This asks whether "flat" Littlewood polynomials exist for all large degrees.
-/
def Erdos228Question : Prop :=
  ∃ (c₁ c₂ : ℝ), c₁ > 0 ∧ c₂ > 0 ∧
  ∀ᶠ n in atTop, ∃ p : Polynomial ℂ,
    p.natDegree = n ∧ IsLittlewoodPolynomial p ∧ IsFlatOnUnitCircle p c₁ c₂

/-! ## Why √n is the expected magnitude -/

/--
**Intuition**: For a random Littlewood polynomial with degree n, evaluated
at z on the unit circle, |P(z)|² is the sum of n terms each of magnitude 1
with random signs. By the central limit theorem, this behaves like √n.

The conjecture asks whether this "random" behavior can be achieved
deterministically with a single polynomial that works for ALL z.
-/
theorem expected_magnitude_heuristic :
    ∀ n : ℕ, n ≥ 1 → Real.sqrt (n : ℝ) > 0 := by
  intro n hn
  exact Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)

/-! ## The Main Theorem -/

/--
**Theorem** (Balister-Bollobás-Morris-Sahasrabudhe-Tiba, 2019):

Flat Littlewood polynomials exist. For every n ≥ 2, there exists a
polynomial P of degree n with coefficients ±1 such that
  c₁√n ≤ |P(z)| ≤ c₂√n
for all |z| = 1, where c₁, c₂ are absolute constants.

This resolved Littlewood's conjecture which had been open since 1966.

The proof uses a probabilistic construction with a sophisticated
derandomization technique.

**Note**: We axiomatize this because the proof requires advanced
harmonic analysis techniques beyond current Mathlib capabilities.
-/
axiom bbmst_theorem : Erdos228Question

/-- The answer to Erdős Problem #228 is YES. -/
theorem erdos_228_answer : Erdos228Question := bbmst_theorem

/-! ## Explicit Formulation -/

/--
Equivalent explicit formulation: there exist universal constants c₁, c₂ > 0
such that for all n ≥ N₀ (some threshold), there exists a degree-n polynomial
with ±1 coefficients whose magnitude on the unit circle is between c₁√n and c₂√n.
-/
axiom bbmst_explicit :
    ∃ (c₁ c₂ : ℝ) (N₀ : ℕ), c₁ > 0 ∧ c₂ > 0 ∧
    ∀ n ≥ N₀, ∃ p : Polynomial ℂ,
      p.natDegree = n ∧
      (∀ i ≤ n, p.coeff i = 1 ∨ p.coeff i = -1) ∧
      (∀ z : ℂ, ‖z‖ = 1 → c₁ * Real.sqrt n ≤ ‖p.eval z‖ ∧ ‖p.eval z‖ ≤ c₂ * Real.sqrt n)

/-! ## Historical Context -/

/--
**Historical note**: The problem has roots going back to Littlewood's 1966
work. Erdős popularized it and it became known as the "Littlewood conjecture"
or the "flat polynomial problem". The 2019 resolution was a major breakthrough.

Key milestones:
- 1966: Littlewood poses the problem
- 1980s-2010s: Various partial results
- 2019: Full resolution by BBMST
-/
axiom littlewood_original :
    ∃ _statement : Prop, True  -- Historical record placeholder

/-! ## Related Problems -/

/--
**Related Problem**: Erdős also asked (Problem 4.31 in Hayman 1974) whether
there exists c > 0 such that max_{|z|=1} |P(z)| > (1+c)√n for all large n.
This asks about the maximum magnitude exceeding √n by a factor.
-/
def ErdosHaymanQuestion : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ n in atTop,
    ∀ p : Polynomial ℂ, p.natDegree = n → IsLittlewoodPolynomial p →
    ∃ z : ℂ, ‖z‖ = 1 ∧ ‖p.eval z‖ > (1 + c) * Real.sqrt n

/-- The Hayman question is related to, but distinct from, the flatness question. -/
axiom hayman_question_status : ErdosHaymanQuestion ∨ ¬ErdosHaymanQuestion

/-! ## Summary -/

/--
**Summary of Erdős Problem #228**:

| Result | Status | Reference |
|--------|--------|-----------|
| Flat Littlewood polynomials exist | SOLVED | BBMST (2019) |
| Original conjecture | Littlewood (1966) | Historical |
| Maximum exceeds √n | Open/Related | Hayman (1974) |
-/
theorem summary_erdos_228 :
    Erdos228Question ∧ (∀ n : ℕ, n ≥ 1 → Real.sqrt (n : ℝ) > 0) := by
  refine ⟨bbmst_theorem, ?_⟩
  intro n hn
  exact Real.sqrt_pos.mpr (by positivity)

end Erdos228
