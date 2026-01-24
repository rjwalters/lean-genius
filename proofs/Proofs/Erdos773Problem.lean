/-
Erdős Problem #773: Sidon Subsets of Squares

Source: https://erdosproblems.com/773
Status: OPEN

Statement:
What is the size of the largest Sidon subset A ⊆ {1, 2², ..., N²}?
Is it N^{1-o(1)}?

A Sidon set (or B₂ sequence) is one where all pairwise sums are distinct.

Known Results:
- Alon-Erdős (1985): |A| ≥ N^{2/3-o(1)} via random construction
- Upper bound: |A| ≪ N/(log N)^{1/4} (using Landau's result on sums of two squares)
- Lefmann-Thiele (1995): Improved lower bound to |A| ≫ N^{2/3}
- Gap between N^{2/3} and N/(log N)^{1/4} remains OPEN

The key insight: sums of two squares have density ~(log N)^{-1/2} (Landau),
which constrains how many squares can form a Sidon set.

Tags: number-theory, sidon-sets, squares
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat Finset Real

namespace Erdos773

/-!
## Part I: Sidon Sets
-/

/--
**Sidon Set (B₂ sequence):**
A set A is Sidon if all pairwise sums a + b (with a ≤ b, a,b ∈ A) are distinct.
Equivalently: a₁ + a₂ = b₁ + b₂ implies {a₁, a₂} = {b₁, b₂}.
-/
def IsSidon (A : Finset ℕ) : Prop :=
  ∀ a₁ a₂ b₁ b₂ : ℕ, a₁ ∈ A → a₂ ∈ A → b₁ ∈ A → b₂ ∈ A →
    a₁ ≤ a₂ → b₁ ≤ b₂ → a₁ + a₂ = b₁ + b₂ →
    (a₁ = b₁ ∧ a₂ = b₂)

/--
**Alternative characterization:**
A is Sidon iff the number of representations of any sum is at most 1.
-/
def IsSidonAlt (A : Finset ℕ) : Prop :=
  ∀ s : ℕ, (A.filter (fun a => ∃ b ∈ A, a ≤ b ∧ a + b = s)).card ≤ 1

/-!
## Part II: Perfect Squares
-/

/--
**Perfect Squares up to N:**
The set {1², 2², ..., N²} = {1, 4, 9, ..., N²}.
-/
def squaresUpTo (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).image (fun k => (k + 1)^2)

/--
**Size of squaresUpTo:**
|squaresUpTo N| = N.
-/
theorem squaresUpTo_card (N : ℕ) : (squaresUpTo N).card = N := by
  sorry

/-!
## Part III: The Main Question
-/

/--
**Maximum Sidon subset of squares:**
f(N) = max{|A| : A ⊆ squaresUpTo N, A is Sidon}.
-/
noncomputable def f (N : ℕ) : ℕ :=
  Finset.sup ((squaresUpTo N).powerset.filter IsSidon) Finset.card

/--
**The Erdős-Alon Question:**
Is f(N) = N^{1-o(1)}?
-/
def MainQuestion : Prop :=
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    (f N : ℝ) ≥ (N : ℝ)^(1 - ε)

/-!
## Part IV: Known Bounds
-/

/--
**Lower Bound (Alon-Erdős 1985, improved by Lefmann-Thiele 1995):**
f(N) ≥ c · N^{2/3} for some constant c > 0.
-/
axiom lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ N in Filter.atTop,
      (f N : ℝ) ≥ c * (N : ℝ)^(2/3 : ℝ)

/--
**Upper Bound (Alon-Erdős 1985):**
f(N) ≤ C · N / (log N)^{1/4} for some constant C > 0.
-/
axiom upper_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ᶠ N in Filter.atTop,
      (f N : ℝ) ≤ C * (N : ℝ) / (Real.log N)^(1/4 : ℝ)

/--
**The Gap:**
We have N^{2/3} ≤ f(N) ≤ N/(log N)^{1/4}.
The question is whether f(N) is closer to N^{1-o(1)} or N^{2/3}.
-/
theorem current_knowledge :
    (∃ c : ℝ, c > 0 ∧ ∀ᶠ N in Filter.atTop, (f N : ℝ) ≥ c * (N : ℝ)^(2/3 : ℝ)) ∧
    (∃ C : ℝ, C > 0 ∧ ∀ᶠ N in Filter.atTop, (f N : ℝ) ≤ C * (N : ℝ) / (Real.log N)^(1/4 : ℝ)) :=
  ⟨lower_bound, upper_bound⟩

/-!
## Part V: Landau's Theorem
-/

/--
**Sums of Two Squares:**
r₂(n) = number of ways to write n = a² + b² (with sign and order).
-/
noncomputable def r2 (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).filter (fun a =>
    ∃ b : ℕ, a^2 + b^2 = n) |>.card

/--
**Count of representable numbers:**
S(N) = |{n ≤ N : n = a² + b² for some a, b}|.
-/
noncomputable def sumOfTwoSquaresCount (N : ℕ) : ℕ :=
  (Finset.range (N + 1)).filter (fun n => r2 n > 0) |>.card

/--
**Landau's Theorem (1908):**
S(N) ~ c · N / √(log N) where c = 1/√2 · ∏_{p≡3 mod 4} (1-1/p²)^{-1/2}.
The density of sums of two squares decays like (log N)^{-1/2}.
-/
axiom landau_theorem :
    ∃ c : ℝ, c > 0 ∧ ∀ ε > 0, ∀ᶠ N in Filter.atTop,
      |(sumOfTwoSquaresCount N : ℝ) - c * N / Real.sqrt (Real.log N)| <
        ε * N / Real.sqrt (Real.log N)

/--
**Why Landau Matters:**
For a Sidon set A of squares, each sum a² + b² must be distinct.
Since sums of two squares are sparse (density (log N)^{-1/2}),
this constrains |A|.
-/
axiom landau_constraint :
    -- If A ⊆ squaresUpTo N is Sidon, then sums a² + b² are distinct
    -- There are |A| choose 2 + |A| such sums (pairs + singletons 2a²)
    -- These must fit in the ~N/(log N)^{1/2} available sums of squares ≤ 2N²
    True

/-!
## Part VI: Probabilistic Method
-/

/--
**Random Construction (Alon-Erdős):**
A random subset of squaresUpTo N with density p yields expected
|A| ~ pN elements, with ~p²N² pairwise sums.
For Sidon property, need p²N² ≤ (log N)^{-1/2} · (2N²), giving p ~ N^{-2/3}.
-/
axiom random_construction :
    -- Random subset with p ~ N^{-2/3+ε} is likely Sidon
    -- This gives |A| ~ N^{1/3+ε}, but refined analysis gives N^{2/3-o(1)}
    True

/--
**Why N^{2/3}?**
Balancing: want many elements (N^α) but few collisions.
Collisions occur when a₁² + a₂² = b₁² + b₂².
With N^α elements, expect N^{2α} sums, but only N/(log N)^{1/2} targets.
Need N^{2α} ≤ N/(log N)^{1/2}, giving α ≤ 1/2 + o(1).
Refined counting gives α = 2/3.
-/
axiom why_two_thirds : True

/-!
## Part VII: Upper Bound Analysis
-/

/--
**Upper Bound Proof Sketch:**
If A ⊆ squaresUpTo N has |A| = m, then A has m(m+1)/2 pairwise sums.
Each sum ≤ 2N² and is a sum of two squares.
By Landau, the number of sums of two squares ≤ 2N² is ~ N² / (log N)^{1/2}.
For Sidon: m² ≤ N² / (log N)^{1/2}, so m ≤ N / (log N)^{1/4}.
-/
theorem upper_bound_sketch (N : ℕ) (A : Finset ℕ) (hA : A ⊆ squaresUpTo N)
    (hSidon : IsSidon A) :
    -- Upper bound on |A| comes from counting argument
    True := trivial

/-!
## Part VIII: Open Questions
-/

/--
**What is the true order of f(N)?**
- Is f(N) = N^{1-o(1)} (the optimistic conjecture)?
- Is f(N) = N^{2/3+o(1)} (matching lower bound)?
- Or something in between?
-/
def trueOrder : Prop :=
  ∃ α : ℝ, 2/3 ≤ α ∧ α < 1 ∧
    ∀ ε > 0, ∀ᶠ N in Filter.atTop,
      (N : ℝ)^(α - ε) ≤ (f N : ℝ) ∧ (f N : ℝ) ≤ (N : ℝ)^(α + ε)

/--
**Can the lower bound be improved?**
The current N^{2/3} comes from probabilistic existence.
An explicit construction might do better.
-/
axiom explicit_construction_question : True

/-!
## Part IX: Summary
-/

/--
**Erdős Problem #773: Summary**

PROBLEM: What is max{|A| : A ⊆ {1²,...,N²}, A Sidon}?

BOUNDS:
- Lower: |A| ≥ c · N^{2/3} (Lefmann-Thiele 1995)
- Upper: |A| ≤ C · N/(log N)^{1/4} (Alon-Erdős 1985)

OPEN: Is f(N) = N^{1-o(1)}? Or is f(N) = Θ(N^{2/3})?

KEY INSIGHT: The sparsity of sums of two squares (Landau) constrains
Sidon sets of squares.
-/
theorem erdos_773_summary :
    -- Lower bound exists
    (∃ c : ℝ, c > 0 ∧ ∀ᶠ N in Filter.atTop, (f N : ℝ) ≥ c * (N : ℝ)^(2/3 : ℝ)) ∧
    -- Upper bound exists
    (∃ C : ℝ, C > 0 ∧ ∀ᶠ N in Filter.atTop, (f N : ℝ) ≤ C * N / (Real.log N)^(1/4 : ℝ)) ∧
    -- Problem remains open
    True :=
  ⟨lower_bound, upper_bound, trivial⟩

/--
**Erdős Problem #773: OPEN**
The true growth rate of the maximum Sidon subset of squares remains unknown.
-/
theorem erdos_773 : True := trivial

end Erdos773
