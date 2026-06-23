/-
Erdős Problem #829: Representations as Sums of Two Cubes

Source: https://erdosproblems.com/829
Status: OPEN

Statement:
Let A ⊂ ℕ be the set of cubes. Is it true that
  1_A ∗ 1_A(n) ≪ (log n)^{O(1)}?

In other words: is the number of representations of n as a sum of two cubes
bounded by some power of log n?

History:
- Mordell: Proved limsup_{n→∞} 1_A ∗ 1_A(n) = ∞ (representation function unbounded)
- Mahler (1935): Proved 1_A ∗ 1_A(n) ≫ (log n)^{1/4} for infinitely many n
- Stewart (2008): Improved to 1_A ∗ 1_A(n) ≫ (log n)^{11/13} for infinitely many n

The question asks if there's an upper bound: 1_A ∗ 1_A(n) ≪ (log n)^c for some c.

References:
- [Ma35b] Mahler, K., "On the Lattice Points on Curves of Genus 1",
  Proc. London Math. Soc. (2) (1935), 431-466.
- [St08] Stewart, C.L., "Cubic Thue equations with many solutions",
  Int. Math. Res. Not. IMRN (2008), Art. ID rnn040, 11.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Finset.Basic

open Real BigOperators

namespace Erdos829

/- ## Part I: Cubes and the Representation Function -/

/--
**Perfect Cube:**
n is a perfect cube if n = k³ for some natural number k.
-/
def IsCube (n : ℕ) : Prop :=
  ∃ k : ℕ, n = k ^ 3

/--
**Set of Cubes:**
A = {1, 8, 27, 64, 125, ...} = {k³ : k ≥ 1}
-/
def CubeSet : Set ℕ := {n | IsCube n}

/--
**Representation Function r₂(n):**
The number of ways to write n as a sum of two cubes.
r₂(n) = |{(a, b) ∈ ℕ² : a³ + b³ = n}|

This is the convolution 1_A ∗ 1_A(n).
-/
def cubeRepresentations (n : ℕ) : ℕ :=
  (Finset.filter (fun p : ℕ × ℕ => p.1 ^ 3 + p.2 ^ 3 = n ∧ p.1 ≤ p.2)
    (Finset.product (Finset.range (n + 1)) (Finset.range (n + 1)))).card

/--
**Full Representation Function (with order):**
Counts ordered pairs (a, b) with a³ + b³ = n.
-/
def orderedCubeRepresentations (n : ℕ) : ℕ :=
  (Finset.filter (fun p : ℕ × ℕ => p.1 ^ 3 + p.2 ^ 3 = n)
    (Finset.product (Finset.range (n + 1)) (Finset.range (n + 1)))).card

/- ## Part II: The Erdős Question -/

/--
**Polynomial Bound on Representations:**
Does r₂(n) grow at most polynomially in log n?
-/
def HasPolylogBound : Prop :=
  ∃ c C : ℝ, c > 0 ∧ C > 0 ∧
    ∀ n : ℕ, n ≥ 2 → (cubeRepresentations n : ℝ) ≤ C * (Real.log n) ^ c

/--
**The Erdős Question:**
Is it true that 1_A ∗ 1_A(n) ≪ (log n)^{O(1)}?

This is asking whether HasPolylogBound holds.
-/
def ErdosQuestion : Prop := HasPolylogBound

/- ## Part III: Known Lower Bounds -/

/--
**Mordell's Theorem:**
The representation function is unbounded:
limsup_{n→∞} r₂(n) = ∞

This shows that there exist n with arbitrarily many representations.
-/
axiom mordell_unbounded :
  ∀ M : ℕ, ∃ n : ℕ, cubeRepresentations n ≥ M

/--
**Infinitely Many Large Values:**
For any fixed k, there exist arbitrarily large n with r₂(n) > k.
-/
/--
**Mahler's Theorem (1935):**
For infinitely many n, r₂(n) ≫ (log n)^{1/4}.
-/
/--
**Stewart's Theorem (2008):**
For infinitely many n, r₂(n) ≫ (log n)^{11/13}.

This is a significant improvement over Mahler's exponent.
-/
axiom stewart_2008 :
  ∃ c : ℝ, c > 0 ∧
    ∀ M : ℕ, ∃ n : ℕ, n ≥ M ∧
      (cubeRepresentations n : ℝ) ≥ c * (Real.log n) ^ (11/13 : ℝ)

/- ## Part IV: Famous Examples -/

/--
**Taxicab Numbers:**
The smallest numbers that can be expressed as sums of two cubes in multiple ways.

Taxicab(2) = 1729 = 1³ + 12³ = 9³ + 10³
(The Hardy-Ramanujan number)
-/
theorem taxicab_1729 : cubeRepresentations 1729 ≥ 2 := by
  -- 1³ + 12³ = 1 + 1728 = 1729
  -- 9³ + 10³ = 729 + 1000 = 1729
  -- This follows from hardy_ramanujan_1729
  have h := hardy_ramanujan_1729
  omega

/--
**1729: The Hardy-Ramanujan Number:**
Famous anecdote: Hardy mentioned taking taxi number 1729, calling it dull.
Ramanujan immediately noted it's the smallest number expressible as sum of
two cubes in two different ways.
-/
theorem hardy_ramanujan_1729 : cubeRepresentations 1729 = 2 := by native_decide

/--
**Taxicab(3) = 87539319:**
The smallest number with 3 representations as sum of two cubes.
87539319 = 167³ + 436³ = 228³ + 423³ = 255³ + 414³
-/
/- ## Part V: Theoretical Framework -/

/--
**Density of Sums of Two Cubes:**
The counting function of numbers representable as sums of two positive cubes
is asymptotically ~ c · x^{2/3} for some constant c.
-/
/--
**Cube-Free Numbers:**
Most integers cannot be expressed as sums of two cubes.
-/
/- ## Part VI: The Gap -/

/--
**Best Known Lower Bound Exponent:**
Stewart's exponent 11/13 ≈ 0.846 is strictly better than Mahler's 1/4 = 0.25.
-/
theorem stewart_improves_mahler : (11 : ℝ) / 13 > (1 : ℝ) / 4 := by norm_num

/- ## Part VII: Summary -/

/--
**Erdős Problem #829:**

PROBLEM: Is 1_A ∗ 1_A(n) ≪ (log n)^{O(1)} where A is the set of cubes?

STATUS: OPEN

KNOWN RESULTS:
1. Mordell: limsup r₂(n) = ∞ (unbounded)
2. Mahler (1935): r₂(n) ≫ (log n)^{1/4} infinitely often
3. Stewart (2008): r₂(n) ≫ (log n)^{11/13} infinitely often

QUESTION: Is there an upper bound r₂(n) ≪ (log n)^c for some constant c?

KEY INSIGHT: The problem is connected to ranks of elliptic curves
x³ + y³ = n, making it deeply arithmetic.
-/
theorem erdos_829_summary :
    -- Stewart's lower bound
    (∃ c : ℝ, c > 0 ∧ ∀ M : ℕ, ∃ n : ℕ, n ≥ M ∧
      (cubeRepresentations n : ℝ) ≥ c * (Real.log n) ^ (11/13 : ℝ)) ∧
    -- Representation function is unbounded
    (∀ M : ℕ, ∃ n : ℕ, cubeRepresentations n ≥ M) :=
  ⟨stewart_2008, mordell_unbounded⟩

end Erdos829
