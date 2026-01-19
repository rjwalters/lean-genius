/-
Erdős Problem #318: Signed Unit Fractions with Zero Sum

Source: https://erdosproblems.com/318
Status: PARTIALLY SOLVED

Statement:
Let A ⊆ ℕ be an infinite arithmetic progression and f : A → {-1, 1} be a
non-constant function. Must there exist a finite non-empty S ⊂ A such that
  ∑_{n ∈ S} f(n)/n = 0?

Variations:
1. What if A is an arbitrary set of positive density?
2. What if A is the set of squares excluding 1?

Known Results:
- Erdős-Straus (1975): TRUE for A = ℕ
- Sattler (1975): TRUE for A = odd numbers
- Sattler (1982b): TRUE for any arithmetic progression
- Counterexample: FALSE for some positive-density sets (e.g., sets with exactly one even)
- Squares case: OPEN (Sattler announced proof but never published)

This is known as "Property P₁" in the literature.

References:
- Erdős, P. and Straus, E.G. (1975): Solution to Problem 387, Nieuw Arch. Wisk.
- Sattler, R. (1975): Solution to Problem 387, Nieuw Arch. Wisk.
- Sattler, R. (1982): On Erdős property P₁ for squarefree numbers
- Sattler, R. (1982b): On Erdős property P₁ for arithmetical sequence
- Erdős, P. and Graham, R. (1980): Old and new problems in combinatorial number theory
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic

open Finset BigOperators

namespace Erdos318

/-
## Part I: Signed Unit Fractions

A signed unit fraction is ±1/n for positive integer n.
-/

/--
**Signed sum of unit fractions:**
Given a finite set S ⊆ ℕ and a sign function f : ℕ → {-1, 1},
compute ∑_{n ∈ S} f(n)/n.
-/
def signedUnitSum (S : Finset ℕ) (f : ℕ → ℤ) : ℚ :=
  ∑ n ∈ S, (f n : ℚ) / (n : ℚ)

/--
**Sign function type:**
A function is a valid sign function if it only takes values ±1.
-/
def IsSignFunction (f : ℕ → ℤ) : Prop :=
  ∀ n : ℕ, f n = 1 ∨ f n = -1

/--
**Non-constant on a set:**
A sign function is non-constant on A if it takes both values.
-/
def IsNonConstant (A : Set ℕ) (f : ℕ → ℤ) : Prop :=
  (∃ a ∈ A, f a = 1) ∧ (∃ b ∈ A, f b = -1)

/-
## Part II: Property P₁

A set A has Property P₁ if every non-constant sign function admits a
finite zero-sum subset.
-/

/--
**Property P₁ (Erdős):**
A set A ⊆ ℕ has Property P₁ if: for every sign function f : A → {-1, 1}
that is non-constant on A, there exists a finite non-empty S ⊆ A with
∑_{n ∈ S} f(n)/n = 0.
-/
def HasPropertyP1 (A : Set ℕ) : Prop :=
  ∀ f : ℕ → ℤ, IsSignFunction f → IsNonConstant A f →
    ∃ S : Finset ℕ, S.Nonempty ∧ (↑S : Set ℕ) ⊆ A ∧ signedUnitSum S f = 0

/-
## Part III: Arithmetic Progressions
-/

/--
**Arithmetic progression:**
The set {a, a+d, a+2d, ...} for a, d > 0.
-/
def arithmeticProgression (a d : ℕ) : Set ℕ :=
  {n : ℕ | ∃ k : ℕ, n = a + k * d}

/--
**The natural numbers:**
The set ℕ⁺ = {1, 2, 3, ...}.
-/
def positiveNaturals : Set ℕ := {n : ℕ | n ≥ 1}

/--
**Odd numbers:**
The set {1, 3, 5, 7, ...}.
-/
def oddNumbers : Set ℕ := {n : ℕ | n % 2 = 1}

/-
## Part IV: Known Results
-/

/--
**Erdős-Straus Theorem (1975):**
The natural numbers have Property P₁.
-/
axiom erdos_straus_1975 : HasPropertyP1 positiveNaturals

/--
**Sattler's Theorem for Odd Numbers (1975):**
The odd numbers have Property P₁.
-/
axiom sattler_odd_1975 : HasPropertyP1 oddNumbers

/--
**Sattler's Main Theorem (1982):**
Every infinite arithmetic progression has Property P₁.
-/
axiom sattler_1982 (a d : ℕ) (ha : a ≥ 1) (hd : d ≥ 1) :
    HasPropertyP1 (arithmeticProgression a d)

/-
## Part V: Main Theorem
-/

/--
**Erdős Problem #318: Arithmetic Progressions**

The answer to the main question is YES: every infinite arithmetic
progression has Property P₁.
-/
theorem erdos_318_arithmetic_progression :
    ∀ a d : ℕ, a ≥ 1 → d ≥ 1 → HasPropertyP1 (arithmeticProgression a d) := by
  intro a d ha hd
  exact sattler_1982 a d ha hd

/-
## Part VI: Positive Density - Counterexamples
-/

/--
**Positive density:**
A set A ⊆ ℕ has positive density if lim inf |A ∩ [1,n]|/n > 0.
-/
def hasPositiveDensity (A : Set ℕ) : Prop :=
  ∃ δ : ℝ, δ > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
    (Finset.filter (· ∈ A) (Finset.range (n + 1))).card ≥ δ * n

/--
**Counterexample construction:**
Sets with exactly one even number fail Property P₁.
-/
def counterexampleSet (m : ℕ) : Set ℕ :=
  {n : ℕ | n % 2 = 1 ∨ n = 2 * m}

/--
**Counterexample has positive density:**
The set of odd numbers plus one even has density 1/2.
-/
theorem counterexample_positive_density (m : ℕ) (hm : m ≥ 1) :
    hasPositiveDensity (counterexampleSet m) := by
  sorry

/--
**Counterexample fails P₁:**
These sets do not have Property P₁.

Intuition: The even number 2m cannot be "canceled" by another even,
and sums of unit fractions with odd denominators have odd denominators
in lowest terms.
-/
axiom counterexample_fails_P1 (m : ℕ) (hm : m ≥ 1) :
    ¬HasPropertyP1 (counterexampleSet m)

/--
**Positive density is not sufficient:**
There exist positive-density sets without Property P₁.
-/
theorem positive_density_insufficient :
    ∃ A : Set ℕ, hasPositiveDensity A ∧ ¬HasPropertyP1 A := by
  use counterexampleSet 1
  constructor
  · exact counterexample_positive_density 1 (by norm_num)
  · exact counterexample_fails_P1 1 (by norm_num)

/-
## Part VII: The Squares Question (OPEN)
-/

/--
**Squares excluding 1:**
The set {4, 9, 16, 25, ...} = {n² : n ≥ 2}.
-/
def squaresExcludingOne : Set ℕ :=
  {n : ℕ | ∃ k : ℕ, k ≥ 2 ∧ n = k^2}

/--
**Why exclude 1:**
We must exclude 1 because ∑_{k≥2} 1/k² < 1, so no finite sum of
+1/k² terms can equal any sum involving -1/1 = -1.
-/
theorem sum_reciprocal_squares_less_than_one :
    ∑' (k : ℕ), (if k ≥ 2 then (1 : ℝ) / k^2 else 0) < 1 := by
  sorry

/--
**Erdős Problem #318: Squares Case (OPEN)**

Does the set of squares excluding 1 have Property P₁?

Sattler announced a proof in 1982 papers but never published it.
This remains an open problem.
-/
def erdos_318_squares_conjecture : Prop :=
  HasPropertyP1 squaresExcludingOne

axiom squares_case_open :
  ¬∃ (proof : erdos_318_squares_conjecture), True

/-
## Part VIII: Key Lemmas and Techniques
-/

/--
**Common denominator technique:**
If ∑_{n ∈ S} f(n)/n = 0, then ∑_{n ∈ S} f(n) · (∏_{m ∈ S} m)/n = 0.

This transforms the rational equation into an integer equation.
-/
theorem zero_sum_integer_form (S : Finset ℕ) (f : ℕ → ℤ) (hS : S.Nonempty)
    (h0 : ∀ n ∈ S, n ≠ 0) (hzero : signedUnitSum S f = 0) :
    ∑ n ∈ S, f n * (∏ m ∈ S, m) / n = 0 := by
  sorry

/--
**Parity obstruction:**
For P₁ to fail, there's typically a parity obstruction from
the denominators.
-/
def parityObstruction (A : Set ℕ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ (∀ a ∈ A, p ∣ a) ∧
    ¬∃ S : Finset ℕ, S.card ≥ 2 ∧ (↑S : Set ℕ) ⊆ A ∧
      (∃ a b : ℕ, a ∈ S ∧ b ∈ S ∧ (∀ q : ℕ, Nat.Prime q → q ∣ a → q ∣ b))

/-
## Part IX: Relationship to Egyptian Fractions
-/

/--
**Egyptian fraction representation:**
Property P₁ is related to signed Egyptian fraction representations.
An Egyptian fraction is a sum of distinct unit fractions.
-/
def isEgyptianRepresentation (S : Finset ℕ) (q : ℚ) : Prop :=
  ∑ n ∈ S, (1 : ℚ) / n = q

/--
**Signed Egyptian fractions:**
With signs, we ask if 0 has a signed Egyptian representation.
-/
def hasSignedZeroRepresentation (A : Set ℕ) (f : ℕ → ℤ) : Prop :=
  ∃ S : Finset ℕ, S.Nonempty ∧ (↑S : Set ℕ) ⊆ A ∧ signedUnitSum S f = 0

/-
## Part X: Main Results Summary
-/

/--
**Erdős Problem #318: Summary**

1. **Arithmetic progressions:** Property P₁ holds (Sattler 1982)
2. **Natural numbers:** Property P₁ holds (Erdős-Straus 1975)
3. **Odd numbers:** Property P₁ holds (Sattler 1975)
4. **Positive density:** NOT sufficient - counterexamples exist
5. **Squares excluding 1:** OPEN

The main question about arithmetic progressions is SOLVED.
The question about squares remains OPEN.
-/
theorem erdos_318_summary :
    -- Arithmetic progressions satisfy P₁
    (∀ a d : ℕ, a ≥ 1 → d ≥ 1 → HasPropertyP1 (arithmeticProgression a d)) ∧
    -- Natural numbers satisfy P₁
    HasPropertyP1 positiveNaturals ∧
    -- Odd numbers satisfy P₁
    HasPropertyP1 oddNumbers ∧
    -- But positive density alone is insufficient
    (∃ A : Set ℕ, hasPositiveDensity A ∧ ¬HasPropertyP1 A) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact erdos_318_arithmetic_progression
  · exact erdos_straus_1975
  · exact sattler_odd_1975
  · exact positive_density_insufficient

/--
**Problem Status:**
- Arithmetic progressions: SOLVED (YES, Sattler 1982)
- Positive density: SOLVED (NO, counterexamples exist)
- Squares: OPEN (announced proof never appeared)
-/
axiom erdos_318_status :
  True  -- Recording the mixed status

end Erdos318
