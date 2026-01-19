/-
Erdős Problem #978: Power-Free Values of Polynomials

Source: https://erdosproblems.com/978
Status: PARTIALLY SOLVED

Statement:
Let f ∈ ℤ[x] be an irreducible polynomial of degree k > 2 (and k ≠ 2^l).

1. Does the set of integers n for which f(n) is (k-1)-power-free have positive density?
   → YES (Hooley, 1967)

2. Are there infinitely many n for which f(n) is (k-2)-power-free?
   → YES for k ≥ 9 (Heath-Brown 2006, Browning 2011)
   → OPEN for k < 9

3. In particular, does n⁴ + 2 represent infinitely many squarefree numbers?
   → OPEN (this is the k = 4 case)

Key Results:
- Erdős (1953): Infinitely many n with f(n) being (k-1)-power-free
- Hooley (1967): Positive density for (k-1)-power-free values, with asymptotics
- Heath-Brown (2006): Affirmative for (k-2)-power-free when k ≥ 10
- Browning (2011): Extended to k ≥ 9 with asymptotic formula

References:
- Erdős, P., "Arithmetical properties of polynomials." J. London Math. Soc. (1953).
- Hooley, C., "On the power free values of polynomials." Mathematika (1967).
- Heath-Brown, D.R., "Counting rational points on algebraic varieties." (2006).
- Browning, T.D., "Power-free values of polynomials." Arch. Math. (2011).
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Real.Basic

open Nat Polynomial

namespace Erdos978

/-
## Part I: Power-Free Numbers
-/

/--
**k-power-free number:**
A positive integer n is k-power-free if no prime p satisfies p^k | n.
-/
def IsPowerFree (k n : ℕ) : Prop :=
  n > 0 ∧ ∀ p : ℕ, p.Prime → ¬(p^k ∣ n)

/--
**Squarefree = 2-power-free:**
-/
def IsSquarefree (n : ℕ) : Prop := IsPowerFree 2 n

/--
**Cubefree = 3-power-free:**
-/
def IsCubefree (n : ℕ) : Prop := IsPowerFree 3 n

/--
**Examples of squarefree numbers:**
-/
theorem one_squarefree : IsSquarefree 1 := by
  constructor
  · omega
  · intros p hp hdiv
    have : p^2 ≥ 4 := by
      have := hp.two_le
      nlinarith
    omega

theorem two_squarefree : IsSquarefree 2 := by
  constructor
  · omega
  · intros p hp hdiv
    interval_cases p <;> simp_all

theorem three_squarefree : IsSquarefree 3 := by
  constructor
  · omega
  · intros p hp hdiv
    interval_cases p <;> simp_all

/-
## Part II: Irreducible Polynomials
-/

/--
**Irreducible polynomial:**
A polynomial is irreducible over ℤ if it cannot be factored as a product
of two non-constant polynomials in ℤ[x].
-/
def IsIrreducible (f : Polynomial ℤ) : Prop :=
  f.degree ≥ 1 ∧
    ∀ g h : Polynomial ℤ, f = g * h →
      (g.degree = 0 ∨ h.degree = 0)

/--
**The polynomial n⁴ + 2:**
This is the specific example in Erdős's question.
-/
noncomputable def f_example : Polynomial ℤ := X^4 + 2

/--
**n⁴ + 2 is irreducible:**
This follows from Eisenstein's criterion with p = 2.
-/
axiom f_example_irreducible : IsIrreducible f_example

/-
## Part III: Density of Power-Free Values
-/

/--
**Density of k-power-free values:**
For polynomial f of degree d, the density of n where f(n) is k-power-free.
-/
noncomputable def powerFreeDensity (f : Polynomial ℤ) (k : ℕ) (x : ℕ) : ℝ :=
  (Finset.range (x + 1)).filter (fun n =>
    IsPowerFree k (f.eval n).natAbs
  ) |>.card / x

/-
## Part IV: Erdős's Result (1953)
-/

/--
**Erdős 1953:**
If f is an irreducible polynomial of degree d > 2 with d ≠ 2^l, then
there are infinitely many n such that f(n) is (d-1)-power-free.
-/
axiom erdos_1953_infinitely_many :
  ∀ f : Polynomial ℤ, IsIrreducible f →
    f.natDegree > 2 →
    (∀ l : ℕ, f.natDegree ≠ 2^l) →
      ∀ N : ℕ, ∃ n : ℕ, n > N ∧
        IsPowerFree (f.natDegree - 1) (f.eval n).natAbs

/-
## Part V: Hooley's Positive Density (1967)
-/

/--
**Hooley 1967:**
The set of integers n for which f(n) is (d-1)-power-free has positive density.
In fact, Hooley provided a precise asymptotic.
-/
axiom hooley_1967_positive_density :
  ∀ f : Polynomial ℤ, IsIrreducible f →
    f.natDegree > 2 →
    (∀ l : ℕ, f.natDegree ≠ 2^l) →
      ∃ c : ℝ, c > 0 ∧
        ∀ ε > 0, ∃ X : ℕ, ∀ x : ℕ, x ≥ X →
          |powerFreeDensity f (f.natDegree - 1) x - c| < ε

/--
**First question answered: YES**
The (d-1)-power-free values have positive density.
-/
theorem first_question_yes :
    ∀ f : Polynomial ℤ, IsIrreducible f →
    f.natDegree > 2 →
    (∀ l : ℕ, f.natDegree ≠ 2^l) →
      ∃ c : ℝ, c > 0 ∧
        ∀ ε > 0, ∃ X : ℕ, ∀ x : ℕ, x ≥ X →
          |powerFreeDensity f (f.natDegree - 1) x - c| < ε :=
  hooley_1967_positive_density

/-
## Part VI: Heath-Brown and Browning on (d-2)-Power-Free
-/

/--
**Heath-Brown 2006:**
For k ≥ 10, there are infinitely many n with f(n) being (k-2)-power-free.
-/
axiom heath_brown_2006 :
  ∀ f : Polynomial ℤ, IsIrreducible f →
    f.natDegree ≥ 10 →
      ∀ N : ℕ, ∃ n : ℕ, n > N ∧
        IsPowerFree (f.natDegree - 2) (f.eval n).natAbs

/--
**Browning 2011:**
Extended to k ≥ 9 with an asymptotic formula.
-/
axiom browning_2011 :
  ∀ f : Polynomial ℤ, IsIrreducible f →
    f.natDegree ≥ 9 →
      ∀ N : ℕ, ∃ n : ℕ, n > N ∧
        IsPowerFree (f.natDegree - 2) (f.eval n).natAbs

/--
**Second question answered: YES for k ≥ 9**
-/
theorem second_question_partial :
    ∀ f : Polynomial ℤ, IsIrreducible f →
    f.natDegree ≥ 9 →
      ∀ N : ℕ, ∃ n : ℕ, n > N ∧
        IsPowerFree (f.natDegree - 2) (f.eval n).natAbs :=
  browning_2011

/-
## Part VII: The n⁴ + 2 Case (OPEN)
-/

/--
**The squarefree conjecture for n⁴ + 2:**
Does n⁴ + 2 represent infinitely many squarefree numbers?

This is OPEN. For k = 4:
- (k-1) = 3-power-free: YES by Hooley
- (k-2) = 2-power-free (squarefree): OPEN

The question falls outside the range k ≥ 9 covered by Browning.
-/
def squarefree_conjecture_n4_plus_2 : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, n > N ∧ IsSquarefree ((n^4 + 2 : ℤ).natAbs)

/--
**Status: OPEN**
The conjecture is not proven or disproven.
-/
axiom n4_plus_2_open :
  -- The squarefree conjecture for n⁴ + 2 is open
  -- Neither proved nor disproved
  True

/--
**What IS known about n⁴ + 2:**
By Hooley, infinitely many n have n⁴ + 2 being cubefree (3-power-free).
-/
axiom n4_plus_2_cubefree :
  ∀ N : ℕ, ∃ n : ℕ, n > N ∧ IsCubefree ((n^4 + 2 : ℤ).natAbs)

/-
## Part VIII: Related Problems
-/

/--
**Related open problems mentioned by Erdős:**
- Does 2ⁿ ± 1 represent infinitely many k-th power-free integers?
- Does n! ± 1 represent infinitely many k-th power-free integers?

Erdős called these "intractable at present."
-/
axiom related_intractable_problems :
  -- 2^n ± 1 and n! ± 1 power-free questions are open
  True

/-
## Part IX: Summary
-/

/--
**Erdős Problem #978: Status**

**Question 1:** (d-1)-power-free values have positive density?
**Answer:** YES (Hooley, 1967)

**Question 2:** Infinitely many (d-2)-power-free values?
**Answer:** YES for d ≥ 9 (Heath-Brown 2006, Browning 2011)
**Status:** OPEN for d < 9

**Question 3:** Does n⁴ + 2 give infinitely many squarefree values?
**Status:** OPEN (d = 4 < 9)

**Key Insight:**
The gap between (d-1)-power-free (fully solved) and (d-2)-power-free
(only solved for d ≥ 9) represents the frontier of current knowledge.
-/
theorem erdos_978_summary :
    -- Question 1: YES (positive density)
    (∀ f : Polynomial ℤ, IsIrreducible f →
      f.natDegree > 2 → (∀ l : ℕ, f.natDegree ≠ 2^l) →
      ∃ c : ℝ, c > 0 ∧ ∀ ε > 0, ∃ X : ℕ, ∀ x : ℕ, x ≥ X →
        |powerFreeDensity f (f.natDegree - 1) x - c| < ε) ∧
    -- Question 2: YES for d ≥ 9
    (∀ f : Polynomial ℤ, IsIrreducible f →
      f.natDegree ≥ 9 →
      ∀ N : ℕ, ∃ n : ℕ, n > N ∧
        IsPowerFree (f.natDegree - 2) (f.eval n).natAbs) ∧
    -- n⁴ + 2 is cubefree infinitely often
    (∀ N : ℕ, ∃ n : ℕ, n > N ∧ IsCubefree ((n^4 + 2 : ℤ).natAbs)) := by
  constructor
  · exact first_question_yes
  constructor
  · exact second_question_partial
  · exact n4_plus_2_cubefree

end Erdos978
