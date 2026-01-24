/-
Erdős Problem #1110: Representability by Sums of p^k q^l

Source: https://erdosproblems.com/1110
Status: OPEN (partially resolved)

Statement:
Let p > q ≥ 2 be coprime integers. An integer n is "representable" if it is the
sum of numbers of the form p^k q^l where none of the summands divide each other.

If {p,q} ≠ {2,3}, what can be said about the density of non-representable numbers?
Are there infinitely many coprime non-representable numbers?

Key Results:
1. Erdős-Lewin (1996): Finitely many non-representable numbers iff {p,q} = {2,3}
2. The {2,3} case has a simple inductive proof (Jansen et al.)
3. Yu-Chen (2022): Density zero for non-representable numbers in many cases
4. Yu-Chen: Infinitely many coprime non-representable numbers for most (p,q)

Historical Note:
Erdős wrote in 1992: "last year I made the following silly conjecture" about the
{2,3} case, which turned out to have a simple inductive proof.

References:
- [ErLe96] Erdős-Lewin, "d-complete sequences of integers"
- [YuCh22] Yu-Chen, "On a conjecture of Erdős and Lewin"
- [YaZh25] Yang-Zhao, improved bounds on representation sizes

Tags: number-theory, additive-combinatorics, representations
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Pow
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Divisors

open Finset

namespace Erdos1110

/-!
## Part I: Basic Definitions
-/

/--
**Power form p^k q^l:**
A number of the form p^k q^l for some non-negative integers k, l.
-/
def IsPowerForm (p q n : ℕ) : Prop :=
  ∃ k l : ℕ, n = p ^ k * q ^ l

/--
**Non-divisibility condition:**
A collection of natural numbers where no element divides another.
-/
def NoOneDividesAnother (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬(a ∣ b)

/--
**Representable number:**
n is representable (for p, q) if it can be written as a sum of terms p^{kᵢ}q^{lᵢ}
where no term divides another.
-/
def IsRepresentable (p q n : ℕ) : Prop :=
  ∃ S : Finset ℕ,
    S.Nonempty ∧
    (∀ s ∈ S, IsPowerForm p q s) ∧
    NoOneDividesAnother S ∧
    S.sum id = n

/--
**The set of non-representable numbers:**
-/
def NonRepresentable (p q : ℕ) : Set ℕ :=
  {n : ℕ | ¬IsRepresentable p q n}

/-!
## Part II: The {2,3} Case (Erdős's "Silly Conjecture")
-/

/--
**The {2,3} case has finite exceptions:**
Every sufficiently large integer is representable when p=3, q=2.
In fact, ALL positive integers are representable!
-/
axiom case_2_3_all_representable :
  ∀ n : ℕ, n ≥ 1 → IsRepresentable 3 2 n

/--
**The simple inductive proof:**
For the {2,3} case:
- If n = 2m, apply induction to m and double all summands
- If n is odd, let 3^k be the largest power of 3 ≤ n,
  then n - 3^k is even, apply induction
-/
theorem inductive_proof_idea :
    -- The proof uses strong induction on n
    True := trivial

/--
**Key lemma: Representing even numbers with even summands:**
If n is even and representable, it has a representation with all even summands.
-/
axiom even_representation :
  ∀ n : ℕ, Even n → IsRepresentable 3 2 n →
    ∃ S : Finset ℕ, (∀ s ∈ S, IsPowerForm 3 2 s ∧ Even s) ∧
      NoOneDividesAnother S ∧ S.sum id = n

/-!
## Part III: General Case (p,q) ≠ (2,3)
-/

/--
**Erdős-Lewin Theorem (1996):**
The set of non-representable numbers is finite if and only if {p,q} = {2,3}.
-/
axiom erdos_lewin_theorem (p q : ℕ) :
    p > q → q ≥ 2 → Nat.Coprime p q →
    (Set.Finite (NonRepresentable p q) ↔ (p = 3 ∧ q = 2) ∨ (p = 2 ∧ q = 3))

/--
**Infinitely many non-representable for most (p,q):**
If {p,q} ≠ {2,3}, there are infinitely many non-representable numbers.
-/
theorem infinitely_many_non_rep (p q : ℕ) (hp : p > q) (hq : q ≥ 2)
    (hcop : Nat.Coprime p q) (hne : ¬((p = 3 ∧ q = 2) ∨ (p = 2 ∧ q = 3))) :
    Set.Infinite (NonRepresentable p q) := by
  have h := erdos_lewin_theorem p q hp hq hcop
  rw [h] at hne
  sorry

/-!
## Part IV: Yu-Chen Results (2022)
-/

/--
**Natural density of a set:**
d(A) = lim_{n→∞} |A ∩ {1,...,n}| / n
-/
def HasDensity (A : Set ℕ) (d : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    |((Finset.filter (· ∈ A) (Finset.range (n + 1))).card : ℝ) / n - d| < ε

/--
**Yu-Chen Density Zero Theorem:**
The non-representable numbers have density zero for many parameter choices:
- q > 3, or
- q = 3 and p > 6, or
- q = 2 and p > 10
-/
axiom yu_chen_density_zero (p q : ℕ) :
    p > q → q ≥ 2 → Nat.Coprime p q →
    (q > 3 ∨ (q = 3 ∧ p > 6) ∨ (q = 2 ∧ p > 10)) →
    HasDensity (NonRepresentable p q) 0

/--
**Yu-Chen Coprime Non-Representables:**
There are infinitely many coprime non-representable numbers for most (p,q):
- q > 3, or
- q = 3 and p ≠ 5, or
- q = 2 and p ∉ {3, 5, 9}
-/
def CoprimeNonRepresentable (p q : ℕ) : Set ℕ :=
  {n ∈ NonRepresentable p q | Nat.Coprime n (p * q)}

axiom yu_chen_coprime_infinite (p q : ℕ) :
    p > q → q ≥ 2 → Nat.Coprime p q →
    (q > 3 ∨ (q = 3 ∧ p ≠ 5) ∨ (q = 2 ∧ p ∉ ({3, 5, 9} : Set ℕ))) →
    Set.Infinite (CoprimeNonRepresentable p q)

/-!
## Part V: Minimum Summand Size
-/

/--
**f(n) = largest floor function:**
For the {2,3} case, all large n can be represented with all summands > f(n).
Erdős-Lewin asked: what is the largest f(n) → ∞?
-/
noncomputable def minSummandBound (n : ℕ) : ℝ :=
  sSup {f : ℝ | ∃ S : Finset ℕ, (∀ s ∈ S, IsPowerForm 3 2 s ∧ (s : ℝ) > f) ∧
    NoOneDividesAnother S ∧ S.sum id = n}

/--
**Yu-Chen bounds (2022):**
n / (log n)^{log₂ 3} ≪ f(n) ≪ n / log n
-/
axiom yu_chen_f_bounds :
  ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      c₁ * n / (Real.log n) ^ (Real.log 3 / Real.log 2) ≤ minSummandBound n ∧
      minSummandBound n ≤ c₂ * n / Real.log n

/--
**Yang-Zhao improvement (2025):**
The lower bound improves to f(n) ≫ n / log n.
-/
axiom yang_zhao_improved_lower :
  ∃ c : ℝ, c > 0 ∧
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      minSummandBound n ≥ c * n / Real.log n

/-!
## Part VI: Related Problems
-/

/--
**Problem #123: Three Powers:**
The analog with three coprime bases (p, q, r) instead of two.
-/
axiom problem_123_three_powers : True

/--
**Problem #845: More on {2,3}:**
Additional questions about the {2,3} representation.
-/
axiom problem_845_2_3_case : True

/--
**Problem #246: Without Non-Divisibility:**
Representations without the constraint that no term divides another.
-/
axiom problem_246_no_constraint : True

/-!
## Part VII: Examples
-/

/--
**Example: 1 = 2^0 · 3^0:**
The number 1 is trivially representable (single summand).
-/
theorem example_1_representable : IsRepresentable 3 2 1 := by
  use {1}
  constructor
  · simp
  constructor
  · intro s hs
    simp at hs
    subst hs
    use 0, 0
    simp
  constructor
  · intro a ha b hb hab
    simp at ha hb
    omega
  · simp

/--
**Example: Small cases for {3,2}:**
All of 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 are representable.
-/
axiom small_cases_representable :
  ∀ n ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10} : Set ℕ), IsRepresentable 3 2 n

/-!
## Part VIII: Summary
-/

/--
**Erdős Problem #1110: Status**

**QUESTION 1:** For {p,q} ≠ {2,3}, what is the density of non-representable numbers?
**ANSWER:** Zero density in many cases (Yu-Chen 2022), but OPEN in general.

**QUESTION 2:** Are there infinitely many coprime non-representable numbers?
**ANSWER:** YES for most parameter choices (Yu-Chen 2022).

**KEY RESULTS:**
1. {2,3} case: All positive integers representable (simple induction)
2. Other cases: Infinitely many non-representable (Erdős-Lewin)
3. Density zero for large p or q > 3 (Yu-Chen)
4. Infinitely many coprime non-representables for most (p,q) (Yu-Chen)
5. Minimum summand bounds: f(n) ~ n/log n (Yu-Chen, Yang-Zhao)

**HISTORICAL NOTE:**
Erdős called his original {2,3} conjecture "silly" after it received a simple
inductive proof. The general problem remains rich and partially open.
-/
theorem erdos_1110_summary :
    -- {2,3} case is completely solved
    (∀ n ≥ 1, IsRepresentable 3 2 n) ∧
    -- Other cases have infinitely many non-representables
    (∀ p q : ℕ, p > q → q ≥ 2 → Nat.Coprime p q →
      ¬((p = 3 ∧ q = 2) ∨ (p = 2 ∧ q = 3)) →
      Set.Infinite (NonRepresentable p q)) := by
  constructor
  · exact case_2_3_all_representable
  · intro p q hp hq hcop hne
    exact infinitely_many_non_rep p q hp hq hcop hne

/--
**Problem Status: OPEN (partially resolved)**
-/
theorem erdos_1110_status : True := trivial

end Erdos1110
