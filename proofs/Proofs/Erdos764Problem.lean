/-
Erdős Problem #764: 3-Fold Convolution Linear Error Bound

Source: https://erdosproblems.com/764
Status: SOLVED (Answer: NO)

Statement:
Let A ⊆ ℕ. Can there exist some constant c > 0 such that
  ∑_{n ≤ N} 1_A * 1_A * 1_A (n) = cN + O(1)?

Answer: NO

This generalizes Erdős-Fuchs (1956) for 2-fold convolutions (Problem #763).
Vaughan (1972) proved that even the weaker bound
  ∑_{n ≤ N} 1_A * 1_A * 1_A (n) = cN + o(N^{1/4} / (log N)^{1/2})
is impossible. His result applies to any h-fold convolution.

Tags: additive-combinatorics, analytic-number-theory, convolutions
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Erdos764

/- ## Part I: Basic Definitions

Characteristic functions and convolutions.
-/

/-- Characteristic function of a set A ⊆ ℕ. -/
def charFun (A : Set ℕ) (n : ℕ) : ℕ := if n ∈ A then 1 else 0

/-- 2-fold convolution: (1_A * 1_A)(n) = #{(a,b) ∈ A × A : a + b = n}. -/
def conv2 (A : Set ℕ) (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun p : ℕ × ℕ => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)
    (Finset.product (Finset.range (n + 1)) (Finset.range (n + 1))))

/-- 3-fold convolution: (1_A * 1_A * 1_A)(n) = #{(a,b,c) ∈ A³ : a + b + c = n}. -/
def conv3 (A : Set ℕ) (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun t : ℕ × ℕ × ℕ =>
    t.1 ∈ A ∧ t.2.1 ∈ A ∧ t.2.2 ∈ A ∧ t.1 + t.2.1 + t.2.2 = n)
    (Finset.product (Finset.range (n + 1))
      (Finset.product (Finset.range (n + 1)) (Finset.range (n + 1)))))

/--
**General h-fold convolution:**
The number of ways to represent n as a sum of h elements from A.
Axiomatized because the general definition requires dependent types.
-/
axiom convH (h : ℕ) (A : Set ℕ) (n : ℕ) : ℕ

/-- Cumulative sum of 2-fold convolution up to N. -/
def sumConv2 (A : Set ℕ) (N : ℕ) : ℕ :=
  Finset.sum (Finset.range (N + 1)) (conv2 A)

/-- Cumulative sum of 3-fold convolution up to N. -/
def sumConv3 (A : Set ℕ) (N : ℕ) : ℕ :=
  Finset.sum (Finset.range (N + 1)) (conv3 A)

/- ## Part II: The Linear Growth Property

What does cN + O(1) mean for convolution sums?
-/

/-- Linear growth with bounded error: f(N) = cN + O(1). -/
def IsLinearBounded (f : ℕ → ℕ) (c : ℝ) : Prop :=
  ∃ M : ℝ, ∀ N : ℕ, |((f N) : ℝ) - c * N| ≤ M

/-- The stronger property: cN + o(N^α). -/
def IsLinearLittleO (f : ℕ → ℕ) (c : ℝ) (α : ℝ) : Prop :=
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, |((f N) : ℝ) - c * N| < ε * (N : ℝ)^α

/-- Even stronger: cN + o(N^{1/4} / (log N)^{1/2}). -/
def IsLinearVaughan (f : ℕ → ℕ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, N ≥ 2 →
    |((f N) : ℝ) - c * N| < ε * (N : ℝ)^(1/4 : ℝ) / Real.sqrt (Real.log N)

/- ## Part III: Erdős-Fuchs Theorem (Problem #763, for context)

The 2-fold case was solved first. Erdős and Fuchs (1956) proved that
no set A can have ∑ 1_A * 1_A = cN + o(N^{1/4} / (log N)^{1/2}).
-/

/--
**Erdős-Fuchs (1956):**
No set has ∑ 1_A * 1_A = cN + o(N^{1/4} / (log N)^{1/2}).
The foundational result for representation function error terms.
-/
/--
**Corollary of Erdős-Fuchs:**
No set has ∑ 1_A * 1_A = cN + O(1).
Since O(1) ⊂ o(N^{1/4} / (log N)^{1/2}), bounded error is also impossible.
-/
/- ## Part IV: Vaughan's Theorem (Problem #764)

Generalization to 3-fold and h-fold convolutions.
-/

/--
**Vaughan (1972):**
No set has ∑ 1_A * 1_A * 1_A = cN + o(N^{1/4} / (log N)^{1/2}).
This is the strong form: even this weak error bound is impossible.
-/
axiom vaughan_3fold_theorem (A : Set ℕ) (c : ℝ) (hc : c > 0) :
  ¬ IsLinearVaughan (sumConv3 A) c

/--
**Corollary of Vaughan's Theorem:**
No set has ∑ 1_A * 1_A * 1_A = cN + O(1).
This is the direct answer to Erdős Problem #764: NO.
-/
axiom vaughan_corollary (A : Set ℕ) (c : ℝ) (hc : c > 0) :
  ¬ IsLinearBounded (sumConv3 A) c

/--
**General h-fold version:**
Vaughan's theorem applies to any h ≥ 2. The convolution sum
∑ 1_A^{*h} cannot be cN + O(1) for any h-fold convolution.
-/
axiom vaughan_hfold_theorem (h : ℕ) (hh : h ≥ 2) (A : Set ℕ) (c : ℝ) (hc : c > 0) :
  ¬ IsLinearBounded (fun N => Finset.sum (Finset.range (N + 1)) (convH h A)) c

/- ## Part V: The Error Lower Bound

The error term must oscillate. It cannot stay bounded,
and in fact must be both large positive and large negative infinitely often.
-/

/-- The error oscillates: infinitely often above N^{1/4} and below -N^{1/4}. -/
def ErrorOscillates (f : ℕ → ℕ) (c : ℝ) : Prop :=
  (∀ N₀ : ℕ, ∃ N ≥ N₀, ((f N) : ℝ) - c * N > (N : ℝ)^(1/4 : ℝ)) ∧
  (∀ N₀ : ℕ, ∃ N ≥ N₀, ((f N) : ℝ) - c * N < -(N : ℝ)^(1/4 : ℝ))

/--
**Error Oscillation:**
For any infinite set A, the error must oscillate by at least N^{1/4}
infinitely often — it cannot even stay on one side.
-/
/- ## Part VI: Examples and Special Cases -/

/-- Square numbers: A = {0, 1, 4, 9, 16, ...}. -/
def Squares : Set ℕ := { n | ∃ k, n = k^2 }

/-- Even for squares, the 3-fold sum cannot be cN + O(1). -/
theorem squares_not_linear (c : ℝ) (hc : c > 0) :
    ¬ IsLinearBounded (sumConv3 Squares) c :=
  vaughan_corollary Squares c hc

/- ## Part VII: Montgomery-Vaughan Refinement

Montgomery and Vaughan (1990) refined the Erdős-Fuchs result.
-/

/--
**Montgomery-Vaughan (1990):**
Refined Erdős-Fuchs to show o(N^{1/4}) is impossible (without the log factor).
-/
/--
**Tightness of the 1/4 exponent:**
There exist sets where the error is O(N^{α}) for any α > 1/4.
The 1/4 exponent is essentially best possible.
-/
/- ## Part VIII: Summary -/

/--
**Erdős Problem #764: Summary**

QUESTION: Can ∑ 1_A * 1_A * 1_A = cN + O(1)?
ANSWER: NO (Vaughan 1972)

Combines:
1. Vaughan's corollary: 3-fold sum cannot be cN + O(1)
2. Vaughan's strong form: cannot even be cN + o(N^{1/4}/(log N)^{1/2})
3. h-fold generalization: applies to any h ≥ 2
-/
theorem erdos_764_summary :
    -- 3-fold sum cannot be cN + O(1)
    (∀ A : Set ℕ, ∀ c : ℝ, c > 0 → ¬ IsLinearBounded (sumConv3 A) c) ∧
    -- Cannot even be cN + o(N^{1/4}/(log N)^{1/2})
    (∀ A : Set ℕ, ∀ c : ℝ, c > 0 → ¬ IsLinearVaughan (sumConv3 A) c) ∧
    -- Generalizes to h-fold
    (∀ h ≥ 2, ∀ A : Set ℕ, ∀ c : ℝ, c > 0 →
      ¬ IsLinearBounded (fun N => Finset.sum (Finset.range (N + 1)) (convH h A)) c) :=
  ⟨fun A c hc => vaughan_corollary A c hc,
   fun A c hc => vaughan_3fold_theorem A c hc,
   fun h hh A c hc => vaughan_hfold_theorem h hh A c hc⟩

end Erdos764
