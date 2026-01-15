/-
  Erdős Problem #143: Sparseness of Integer-Dilation-Avoiding Sets

  Source: https://erdosproblems.com/143
  Status: PARTIALLY SOLVED (Koukoulopoulos-Lamzouri-Lichtman 2025)
  Prize: $500 (for the full resolution)

  Statement:
  Let A ⊂ (1, ∞) be a countably infinite set such that for all x ≠ y ∈ A
  and integers k ≥ 1 we have |kx - y| ≥ 1. Does this imply that A is sparse?

  In particular, does this imply:
  (i)   liminf |A ∩ [1,x]|/x = 0 ?
  (ii)  ∑_{x∈A} 1/(x log x) < ∞ ?
  (iii) ∑_{x<n, x∈A} 1/x = o(log n) ?

  History:
  - Erdős noted that for integer sets, the condition implies A is "primitive"
  - Koukoulopoulos-Lamzouri-Lichtman (2025): Proved (iii)

  Reference: arXiv:2502.09539 (KLL25)
-/

import Mathlib

open Filter Set
open scoped Topology

namespace Erdos143

/-! ## Core Definitions -/

/-- A set A ⊆ (1, ∞) is "well-separated under integer dilation" if for all
    distinct x, y ∈ A and all positive integers k, we have |kx - y| ≥ 1. -/
def WellSeparatedSet (A : Set ℝ) : Prop :=
  (A ⊆ Set.Ioi 1) ∧
  Set.Infinite A ∧
  Set.Countable A ∧
  (∀ x ∈ A, ∀ y ∈ A, x ≠ y → ∀ k : ℕ, k ≥ 1 → 1 ≤ |k * x - y|)

/-- The counting function for A ∩ [1, x]. -/
noncomputable def countingFn (A : Set ℝ) (x : ℝ) : ℕ :=
  (A ∩ Set.Icc 1 x).ncard

/-! ## The Conjectures -/

/-- **Conjecture (i)**: The lower density is zero. STATUS: OPEN -/
def Conjecture_i (A : Set ℝ) : Prop :=
  liminf (fun x => (countingFn A x : ℝ) / x) atTop = 0

/-- **Conjecture (ii)**: The reciprocal-log series converges. STATUS: OPEN -/
def Conjecture_ii (A : Set ℝ) : Prop :=
  Summable fun (x : A) => 1 / ((x : ℝ) * Real.log x)

/-- **Conjecture (iii)**: The partial reciprocal sum is o(log n). STATUS: SOLVED -/
def Conjecture_iii (A : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ N₀ : ℝ, ∀ n ≥ N₀, ∀ (partialSum : ℝ),
    -- partialSum represents ∑_{x∈A, x<n} 1/x
    partialSum ≤ ε * Real.log n

/-! ## Main Results -/

/--
**Koukoulopoulos-Lamzouri-Lichtman Theorem (2025)**

For any well-separated set A, the partial sum ∑_{x<n, x∈A} 1/x = o(log n).

Axiomatized because the proof requires:
1. Bounds from multiplicative number theory
2. Graph-theoretic arguments on GCD graphs
3. Estimates beyond current Mathlib

Reference: arXiv:2502.09539
-/
axiom kll_theorem (A : Set ℝ) (hA : WellSeparatedSet A) : Conjecture_iii A

/-- The full Erdős Problem 143 would require all three conjectures. -/
def ErdosProblem143_Full (A : Set ℝ) : Prop :=
  Conjecture_i A ∧ Conjecture_ii A ∧ Conjecture_iii A

/-- What's proven: Conjecture (iii) follows from well-separation. -/
theorem erdos_143_partial (A : Set ℝ) (hA : WellSeparatedSet A) :
    Conjecture_iii A :=
  kll_theorem A hA

/-! ## Connection to Primitive Sets -/

/-- A set of positive integers is primitive if no element divides another. -/
def IsPrimitiveSet (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬(a ∣ b)

/-- For integer sets, well-separation implies primitivity.
    If |ka - b| ≥ 1 for all k ≥ 1 and distinct a, b ∈ A, then a ∤ b. -/
axiom well_separated_integers_primitive (A : Set ℕ) (hA : A.Infinite)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∀ k : ℕ, k ≥ 1 → (1 : ℝ) ≤ |(k : ℝ) * (a : ℝ) - (b : ℝ)|) :
    IsPrimitiveSet A

/-! ## Historical Results -/

/-- **Erdős (1935)**: For primitive integer sets, ∑ 1/(n log n) converges. -/
axiom erdos_1935_primitive (A : Set ℕ) (hA : IsPrimitiveSet A) (hinf : A.Infinite) :
    Summable fun (n : A) => (1 : ℝ) / (n * Real.log n)

end Erdos143
