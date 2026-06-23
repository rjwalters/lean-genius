/-
Erdős Problem #206: Eventually Greedy Egyptian Fraction Underapproximations

Source: https://erdosproblems.com/206
Status: SOLVED (Disproved by Kovač 2024)

Statement:
Let x > 0 be a real number. For any n >= 1 let
  R_n(x) = max { sum 1/m_i : distinct positive integers m_i, sum < x }
be the maximal sum of n distinct unit fractions which is < x.

Question:
Is it true that, for almost all x, for sufficiently large n, we have
  R_{n+1}(x) = R_n(x) + 1/m,
where m is minimal such that m does not appear in R_n(x) and the
right-hand side is < x?

Answer: NO (Kovač 2024)
The set of x in (0, infinity) for which best underapproximations are
eventually greedy has Lebesgue measure ZERO.

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
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Nat Finset Set MeasureTheory

namespace Erdos206

/- ## Part I: Basic Definitions -/

/-- **Egyptian Fraction:**
    A sum of distinct unit fractions: 1/m_1 + 1/m_2 + ... + 1/m_n
    where all m_i are distinct positive integers. -/
def EgyptianFraction (S : Finset ℕ) : ℝ :=
  S.sum (fun m => if m = 0 then 0 else (1 : ℝ) / m)

/-- **Valid Denominators:**
    For an Egyptian fraction sum, denominators must be positive integers. -/
def validDenominators (S : Finset ℕ) : Prop :=
  ∀ m ∈ S, m > 0

/-- **Best n-term Underapproximation R_n(x):**
    The maximum sum of n distinct unit fractions that is strictly less than x.
    Axiomatized because the full definition involves a supremum over
    finite subsets of positive integers with a cardinality constraint. -/
axiom R (n : ℕ) (x : ℝ) : ℝ

/- ## Part II: The Greedy Property -/

/-- **Eventually Greedy at x:**
    x has the eventually greedy property if there exists N such that
    for all n >= N, R_{n+1}(x) = R_n(x) + 1/m where m is the greedy
    choice (the smallest positive integer not yet used such that
    the sum stays below x). -/
def EventuallyGreedy (x : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∃ m > 0,
    R (n + 1) x = R n x + (1 : ℝ) / m ∧
    -- m is the smallest valid choice
    (∀ k, 0 < k → k < m → R n x + (1 : ℝ) / k ≥ x)

/-- **The Set of Eventually Greedy Numbers:**
    G = { x in (0, infinity) : x is eventually greedy } -/
def EventuallyGreedySet : Set ℝ := { x | x > 0 ∧ EventuallyGreedy x }

/- ## Part III: Positive Results -/

/-- **Curtiss (1922): x = 1 is eventually greedy.**
    The best underapproximations to 1 eventually follow the greedy algorithm.
    This was the first result of this type. -/
axiom curtiss_theorem : EventuallyGreedy 1

/-- **Erdős (1950): x = 1/m is eventually greedy for all positive m.**
    This extended Curtiss's result to all unit fraction targets. -/
axiom erdos_unit_fractions (m : ℕ) (hm : m > 0) :
    EventuallyGreedy (1 / m)

/- ## Part IV: Kovač's Theorem (2024) - The Main Result -/

/-- **Kovač's Theorem (2024): DISPROVED**

    The set of x in (0, infinity) for which best underapproximations are
    eventually greedy has Lebesgue measure ZERO.

    This is "as false as possible" - almost all numbers are NOT eventually
    greedy. The conjecture fails in the strongest measure-theoretic sense. -/
axiom kovac_theorem :
    volume EventuallyGreedySet = 0

/-- **The Answer to Erdős Problem #206: NO**

    The conjecture that "for almost all x, best underapproximations are
    eventually greedy" is FALSE. In fact, the opposite is true:
    for almost all x, best underapproximations are NOT eventually greedy. -/
theorem erdos_206_answer : volume EventuallyGreedySet = 0 := kovac_theorem

/- ## Part V: Open Questions -/

/-- **Open Question 1: All Rationals.**
    Is every positive rational x eventually greedy?
    Known for specific classes (unit fractions, a/b with a|b+1)
    but not for all rationals. -/
def all_rationals_eventually_greedy : Prop :=
  ∀ (p q : ℤ), q > 0 → (p : ℝ) / q > 0 → EventuallyGreedy ((p : ℝ) / q)

/-- **Open Question 2: Explicit Non-Greedy Example.**
    Despite knowing almost all x are not eventually greedy,
    no explicit example of a non-greedy number has been constructed.
    Erdős and Graham claimed it is "not difficult" to find one,
    but no proof or reference was ever given. -/
def explicit_nongreedy_example_exists : Prop :=
  ∃ x : ℝ, x > 0 ∧ ¬EventuallyGreedy x

/- ## Part VI: Special Cases and Counterexample -/

/-- **Non-greedy at finite step: the 11/24 example.**

    R_1(11/24) = 1/3 (the largest unit fraction below 11/24)
    R_2(11/24) = 1/4 + 1/5 = 9/20 = 0.45

    If greedy continued from R_1: 1/3 + 1/m needs 1/m < 11/24 - 1/3 = 3/24 = 1/8
    So greedy would give 1/3 + 1/9 = 4/9 ≈ 0.444
    But 1/4 + 1/5 = 9/20 = 0.45 > 4/9 -/

/- ## Part VII: Connection to Egyptian Fractions -/

/-- **Sylvester's Greedy Algorithm:**
    Given x > 0 with x < 1, compute the next denominator as ceil(1/x)
    and subtract the corresponding unit fraction. Iterating this
    produces an Egyptian fraction representation (always terminates
    for rationals). -/
def sylvesterStep (x : ℝ) (hx : x > 0) (hx1 : x < 1) : ℕ × ℝ :=
  let m := Nat.ceil (1 / x)
  (m, x - 1 / m)

/- ## Part VIII: Summary -/

/-- **Summary: Main results combined.**
    The answer is NO, but specific cases are greedy. -/
theorem erdos_206_summary :
    -- The main question is answered: NO
    volume EventuallyGreedySet = 0 ∧
    -- But specific cases (x=1, x=1/m) are greedy
    EventuallyGreedy 1 ∧
    (∀ m > 0, EventuallyGreedy (1 / m : ℝ)) := by
  refine ⟨kovac_theorem, curtiss_theorem, ?_⟩
  intro m hm
  exact erdos_unit_fractions m hm

/-- **Erdős Problem #206: SOLVED (Disproved)**

    QUESTION: For almost all x > 0, are the best underapproximations
    by Egyptian fractions eventually constructed greedily?

    ANSWER: NO (Kovač 2024)

    The set of x with the eventually greedy property has Lebesgue
    measure zero. Despite this, no explicit example of a non-greedy
    number is known.

    KNOWN TO BE GREEDY:
    - x = 1 (Curtiss 1922)
    - x = 1/m for all positive m (Erdős 1950)
    - x = a/b when a | b+1 (Nathanson 2023)
    - Extended classes of rationals (Chu 2023)

    OPEN:
    - Are all rationals eventually greedy?
    - Construct an explicit non-greedy number -/
theorem erdos_206 : volume EventuallyGreedySet = 0 := kovac_theorem

end Erdos206
