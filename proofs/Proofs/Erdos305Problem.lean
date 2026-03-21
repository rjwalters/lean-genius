/-
Erdős Problem #305: Maximum Denominator in Egyptian Fraction Representations

Source: https://erdosproblems.com/305
Status: SOLVED (Yokota 1988, improved by Liu-Sawhney 2024)

Statement:
For integers 1 ≤ a < b, let D(a,b) be the minimal value of n_k such that there
exist integers 1 ≤ n₁ < n₂ < ... < n_k with:
    a/b = 1/n₁ + 1/n₂ + ... + 1/n_k

Define D(b) = max_{1 ≤ a < b} D(a,b).
Is it true that D(b) ≪ b(log b)^{1+o(1)}?

Solution:
- Bleicher-Erdős (1976): D(b) ≪ b(log b)²
- Lower bound: D(p) ≫ p log p for prime p
- Yokota (1988): D(b) ≪ b(log b)(log log b)⁴(log log log b)²
- Liu-Sawhney (2024): D(b) ≪ b(log b)(log log b)³(log log log b)^{O(1)}

Background:
- Egyptian fractions = sums of distinct unit fractions
- Every rational in (0,1] has an Egyptian fraction representation
- The problem asks: how large must denominators get?
- Related to the greedy algorithm (Fibonacci-Sylvester expansion)

References:
- Bleicher, Erdős (1976): "Denominators of unit fractions", J. Number Th.
- Yokota (1988): "On a problem of Bleicher and Erdős", J. Number Theory
- Liu, Sawhney (2024): "On further questions regarding unit fractions", arXiv
- Erdős, Graham (1980): Problem E30 in "Old and New Problems in Combinatorics"
-/

import Mathlib.Tactic

open Finset

namespace Erdos305

/-
## Part I: Egyptian Fractions
-/

/--
**Egyptian Fraction:**
A sum of distinct unit fractions 1/n₁ + 1/n₂ + ... + 1/n_k where n₁ < n₂ < ... < n_k.
Named after ancient Egyptian mathematics where all fractions were written this way.
-/
def isEgyptianFraction (S : Finset ℕ) : Prop :=
  ∀ n ∈ S, n ≥ 1

/--
**Sum of Unit Fractions:**
Given a finite set S of positive integers, compute ∑_{n ∈ S} 1/n.
-/
noncomputable def unitFractionSum (S : Finset ℕ) : ℚ :=
  S.sum fun n => if n = 0 then 0 else 1 / n

/--
**Egyptian Representation:**
A set S represents rational a/b as an Egyptian fraction if
∑_{n ∈ S} 1/n = a/b with all denominators distinct positive integers.
-/
def isEgyptianRepresentation (S : Finset ℕ) (a b : ℕ) : Prop :=
  a < b ∧ b > 0 ∧ isEgyptianFraction S ∧ unitFractionSum S = a / b

/--
**Existence Theorem:**
Every positive rational < 1 has an Egyptian fraction representation.
This was known to the ancient Egyptians and follows from the greedy algorithm.
-/
axiom egyptian_representation_exists (a b : ℕ) (hab : 0 < a) (hlt : a < b) :
  ∃ S : Finset ℕ, isEgyptianRepresentation S a b

/-
## Part II: The D(a,b) Function
-/

/--
**Maximum Denominator:**
For a finite set S, the maximum element.
-/
def maxDenominator (S : Finset ℕ) : ℕ :=
  S.sup id

/--
**D(a,b) Function:**
The minimum possible maximum denominator over all Egyptian fraction
representations of a/b.
-/
noncomputable def D_ab (a b : ℕ) : ℕ :=
  if _ : a < b ∧ b > 0 then
    sInf { maxDenominator S | S ∈ {S : Finset ℕ | isEgyptianRepresentation S a b} }
  else 0

/--
**D(b) Function:**
D(b) = max_{1 ≤ a < b} D(a,b)
The worst-case maximum denominator needed for any fraction with denominator b.
-/
noncomputable def D_b (b : ℕ) : ℕ :=
  if h : b > 1 then
    Finset.sup (Finset.range (b - 1)) fun a => D_ab (a + 1) b
  else 0

/-
## Part III: The Erdős Conjecture
-/

/--
**Erdős's Conjecture:**
Is D(b) ≪ b(log b)^{1+o(1)}?

The lower bound D(p) ≫ p log p shows we need at least (log b)¹.
The conjecture asks if this is essentially tight.
-/
def erdos305Conjecture : Prop :=
  ∀ ε > 0, ∃ C : ℝ, C > 0 ∧ ∀ b : ℕ, b ≥ 2 →
    (D_b b : ℝ) ≤ C * b * (Real.log b)^(1 + ε)

/--
**Status: Essentially Solved:**
Yokota (1988) proved D(b) ≪ b(log b)(log log b)⁴(log log log b)².
This confirms D(b) ≪ b(log b)^{1+o(1)} since (log log b)⁴(log log log b)² = (log b)^{o(1)}.
-/
theorem erdos_305_solved : erdos305Conjecture := by
  intro ε hε
  -- The bounds from Yokota/Liu-Sawhney show D(b) ≪ b(log b)^{1+o(1)}
  sorry

/-
## Part IV: The Greedy Algorithm
-/

/--
**Greedy (Fibonacci-Sylvester) Algorithm:**
To represent a/b, subtract the largest unit fraction 1/n ≤ a/b,
then repeat on the remainder.

Choose n = ⌈b/a⌉, so 1/n ≤ a/b < 1/(n-1).
-/
def greedyStep (a b : ℕ) : ℕ × ℕ × ℕ :=
  if a = 0 ∨ b = 0 then (0, 0, 0)
  else
    let n := (b + a - 1) / a  -- ceiling of b/a
    let newA := a * n - b
    let newB := b * n
    (n, newA, newB)

/-
## Part V: Summary
-/

/--
**Erdős Problem #305: Statement**
For 1 ≤ a < b, let D(a,b) = min max denominator over all Egyptian representations
of a/b. Let D(b) = max_{a < b} D(a,b).
Is D(b) ≪ b(log b)^{1+o(1)}?
-/
def erdos305Problem : Prop :=
  erdos305Conjecture

/--
**Erdős Problem #305: Solution**
Yokota (1988) proved D(b) ≪ b(log b)(log log b)⁴(log log log b)².
Liu-Sawhney (2024) improved to (log log b)³(log log log b)^{O(1)}.
Both confirm D(b) ≪ b(log b)^{1+o(1)}.
-/
theorem erdos_305 : erdos305Problem := erdos_305_solved

/--
**Summary:**
Erdős Problem #305 asked whether the maximum denominator needed for
Egyptian fraction representations satisfies D(b) ≪ b(log b)^{1+o(1)}.

The answer is YES:
- Lower bound: D(p) ≫ p log p for prime p (so log b factor is necessary)
- Upper bound: D(b) ≪ b(log b)(log log b)³(log log log b)^{O(1)} (Liu-Sawhney)

The extra iterated log factors are (log b)^{o(1)}, confirming the conjecture.

Status: SOLVED (Yokota 1988, improved Liu-Sawhney 2024)
-/
theorem erdos_305_summary : erdos305Problem := erdos_305_solved

end Erdos305
