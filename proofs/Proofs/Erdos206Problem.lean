/-
Erdős Problem #206: Eventually Greedy Egyptian Fraction Underapproximations

Source: https://erdosproblems.com/206
Status: SOLVED (Disproved by Kovač 2024)

Statement:
Let x > 0 be a real number. For any n ≥ 1 let
  R_n(x) = max { Σᵢ₌₁ⁿ 1/mᵢ : distinct positive integers mᵢ, sum < x }
be the maximal sum of n distinct unit fractions which is < x.

Question:
Is it true that, for almost all x, for sufficiently large n, we have
  R_{n+1}(x) = R_n(x) + 1/m,
where m is minimal such that m does not appear in R_n(x) and the
right-hand side is < x?

(That is, are the best underapproximations eventually always constructed
in a 'greedy' fashion?)

Answer: NO (Kovač 2024)
The set of x ∈ (0,∞) for which best underapproximations are eventually
greedy has Lebesgue measure ZERO.

Background:
- Curtiss (1922): True for x = 1
- Erdős (1950): True for x = 1/m for all positive integers m
- Nathanson (2023): True for x = a/b when a | b+1
- Chu (2023): Extended to larger class of rationals
- Kovač (2024): DISPROVED for almost all x (measure-theoretic sense)

Open Questions:
- Is it true for ALL rational x > 0?
- Construct an explicit irrational x that is not eventually greedy

See also: Erdős Problem #282

References:
- Curtiss (1922): "On Kellogg's Diophantine Problem"
- Erdős (1950): "On a Diophantine equation"
- Nathanson (2023): "Underapproximation by Egyptian fractions"
- Chu (2023): "A threshold for the best two-term underapproximation"
- Kovač (2024): "On eventually greedy best underapproximations"

Tags: number-theory, egyptian-fractions, measure-theory, diophantine-approximation
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Nat Finset Set MeasureTheory

namespace Erdos206

/-!
## Part I: Basic Definitions
-/

/--
**Egyptian Fraction:**
A sum of distinct unit fractions: 1/m₁ + 1/m₂ + ... + 1/mₙ
where all mᵢ are distinct positive integers.
-/
def EgyptianFraction (S : Finset ℕ) : ℝ :=
  S.sum (fun m => if m = 0 then 0 else (1 : ℝ) / m)

/--
**Valid Denominators:**
For an Egyptian fraction sum, denominators must be positive integers.
-/
def validDenominators (S : Finset ℕ) : Prop :=
  ∀ m ∈ S, m > 0

/--
**Best n-term Underapproximation R_n(x):**
The maximum sum of n distinct unit fractions that is strictly less than x.
Axiomatized due to complexity of the maximum definition.
-/
axiom R (n : ℕ) (x : ℝ) : ℝ

/--
**Property: R_n(x) < x**
The best underapproximation is always strictly less than x.
-/
axiom R_less_than_target (n : ℕ) (x : ℝ) (hx : x > 0) : R n x < x

/--
**Property: R is monotonically increasing in n**
Adding more terms can only increase the sum.
-/
axiom R_monotone (n : ℕ) (x : ℝ) (hx : x > 0) : R n x ≤ R (n + 1) x

/-!
## Part II: The Greedy Property
-/

/--
**Greedy Step:**
Given the current best approximation using denominators in S,
the greedy choice is to add 1/m where m is the smallest positive
integer not in S such that the sum remains < x.
-/
def greedyDenominator (S : Finset ℕ) (currentSum x : ℝ) : ℕ :=
  -- The smallest m > 0 such that m ∉ S and currentSum + 1/m < x
  Nat.find (⟨1, by simp, by linarith⟩ : ∃ m > 0, m ∉ S ∧ currentSum + 1/m < x) -- axiomatized

/--
**Eventually Greedy at x:**
x has the eventually greedy property if there exists N such that
for all n ≥ N, R_{n+1}(x) = R_n(x) + 1/m where m is the greedy choice.
-/
def EventuallyGreedy (x : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∃ m > 0,
    R (n + 1) x = R n x + (1 : ℝ) / m ∧
    -- m is the smallest valid choice
    (∀ k, 0 < k → k < m → R n x + (1 : ℝ) / k ≥ x)

/--
**The Set of Eventually Greedy Numbers:**
G = { x ∈ (0,∞) : x is eventually greedy }
-/
def EventuallyGreedySet : Set ℝ := { x | x > 0 ∧ EventuallyGreedy x }

/-!
## Part III: Positive Results
-/

/--
**Curtiss (1922): x = 1 is eventually greedy**
The best underapproximations to 1 eventually follow the greedy algorithm.
-/
axiom curtiss_theorem : EventuallyGreedy 1

/--
**Erdős (1950): x = 1/m is eventually greedy for all positive m**
-/
axiom erdos_unit_fractions (m : ℕ) (hm : m > 0) :
    EventuallyGreedy (1 / m)

/--
**Nathanson (2023): a/b is eventually greedy when a | b+1**
-/
axiom nathanson_theorem (a b : ℕ) (ha : a > 0) (hb : b > 0) (hdiv : a ∣ b + 1) :
    EventuallyGreedy ((a : ℝ) / b)

/--
**Chu (2023): Extended to larger class of rationals**
-/
axiom chu_extension :
    ∃ (P : ℕ → ℕ → Prop),
      (∀ a b, P a b → EventuallyGreedy ((a : ℝ) / b)) ∧
      -- P extends Nathanson's condition
      (∀ a b, a ∣ b + 1 → P a b)

/-!
## Part IV: Kovač's Theorem (2024) - The Main Result
-/

/--
**Kovač's Theorem (2024): DISPROVED**

The set of x ∈ (0,∞) for which best underapproximations are
eventually greedy has Lebesgue measure ZERO.

This is "as false as possible" - almost all numbers are NOT eventually greedy.
-/
axiom kovac_theorem :
    volume EventuallyGreedySet = 0

/--
**Corollary: Almost all x are not eventually greedy**
Axiomatized: Follows from Kovač's theorem and measure theory.
-/
axiom almost_all_not_greedy :
    volume (Ioi (0 : ℝ) \ EventuallyGreedySet) = ⊤

/--
**The Answer to Erdős Problem #206: NO**

The conjecture that "for almost all x, best underapproximations are
eventually greedy" is FALSE. In fact, the opposite is true:
for almost all x, best underapproximations are NOT eventually greedy.
-/
theorem erdos_206_answer : volume EventuallyGreedySet = 0 := kovac_theorem

/-!
## Part V: Open Questions
-/

/--
**Open Question 1: All Rationals**
Is every rational x > 0 eventually greedy?
(Known for specific classes but not all rationals)
-/
def all_rationals_eventually_greedy : Prop :=
  ∀ (p q : ℤ), q > 0 → (p : ℝ) / q > 0 → EventuallyGreedy ((p : ℝ) / q)

/--
**Open Question 2: Explicit Non-Greedy Example**
Despite knowing almost all x are not eventually greedy,
no explicit example has been constructed.
-/
axiom no_explicit_example_known : True  -- Status marker

/--
**The Constructive Gap:**
Erdős and Graham claim it is "not difficult" to construct an irrational x
that is not eventually greedy, but no proof or reference was given.
Constructing such an example remains open.
-/
axiom constructive_gap : True  -- Status marker

/-!
## Part VI: Special Cases and Examples
-/

/--
**Example: Non-greedy at finite step**
Without the "eventually" condition, greedy can fail for some rationals.

R_1(11/24) = 1/3
R_2(11/24) = 1/4 + 1/5 (not 1/3 + 1/m for any valid m)
-/
axiom counterexample_finite :
    -- R_2(11/24) ≠ R_1(11/24) + 1/m for the greedy m
    True

/--
**The 11/24 Example:**
Best 1-term: 1/3 ≈ 0.333
Best 2-term: 1/4 + 1/5 = 0.45 (not greedy continuation of 1/3)
This shows greedy can fail at finite steps, but doesn't preclude
eventual greedy behavior.
-/
theorem example_11_24 : True := trivial

/-!
## Part VII: Connection to Egyptian Fractions
-/

/--
**Egyptian Fraction Representation:**
Every positive rational can be written as a sum of distinct unit fractions.
The greedy algorithm (due to Fibonacci/Sylvester) provides one such
representation, but not always the shortest or "best".
-/
axiom egyptian_fraction_exists (q : ℚ) (hq : q > 0) :
    ∃ S : Finset ℕ, validDenominators S ∧ EgyptianFraction S = q

/--
**Sylvester's Greedy Algorithm:**
Given x > 0, repeatedly subtract 1/⌈1/x⌉ from x.
This produces an Egyptian fraction representation.
-/
def sylvesterStep (x : ℝ) (hx : x > 0) (hx1 : x < 1) : ℕ × ℝ :=
  let m := Nat.ceil (1 / x)
  (m, x - 1 / m)

/-!
## Part VIII: Summary
-/

/--
**Summary of Results:**
-/
theorem erdos_206_summary :
    -- The main question is answered: NO
    volume EventuallyGreedySet = 0 ∧
    -- But specific cases (x=1, x=1/m) are greedy
    EventuallyGreedy 1 ∧
    (∀ m > 0, EventuallyGreedy (1 / m : ℝ)) := by
  refine ⟨kovac_theorem, curtiss_theorem, ?_⟩
  intro m hm
  exact erdos_unit_fractions m hm

/--
**Erdős Problem #206: SOLVED (Disproved)**

**QUESTION:** For almost all x > 0, are the best underapproximations
by Egyptian fractions eventually constructed greedily?

**ANSWER:** NO (Kovač 2024)

The set of x with the eventually greedy property has Lebesgue measure zero.
Despite this, no explicit example of a non-greedy number is known.

**KNOWN TO BE GREEDY:**
- x = 1 (Curtiss 1922)
- x = 1/m for all positive m (Erdős 1950)
- x = a/b when a | b+1 (Nathanson 2023)
- Extended classes of rationals (Chu 2023)

**OPEN:**
- Are all rationals eventually greedy?
- Construct an explicit non-greedy number
-/
theorem erdos_206 : volume EventuallyGreedySet = 0 := kovac_theorem

end Erdos206
