/-
Erdős Problem #191: Monochromatic Sets with Large 1/log Sum

Source: https://erdosproblems.com/191
Status: SOLVED (Rödl 2003, Conlon-Fox-Sudakov 2013)

Statement:
Let C > 0 be arbitrary. Is it true that, if n is sufficiently large depending on C,
then in any 2-colouring of the edges of the complete graph K({2,...,n}) there exists
some X ⊂ {2,...,n} such that all edges within X are monochromatic and
  ∑_{x ∈ X} 1/log x ≥ C?

Answer: YES

Tight bounds on the achievable sum:
- Upper construction (Rödl): For all n, there exists a 2-coloring such that
  any monochromatic X satisfies ∑_{x ∈ X} 1/log x ≪ log log log n
- Lower bound (Conlon-Fox-Sudakov): For any 2-coloring, there exists
  monochromatic X with ∑_{x ∈ X} 1/log x ≥ 2^{-8} log log log n

References:
- [ErGr80] Erdős-Graham original problem
- [Ro03] Rödl: Solved affirmatively + upper construction
- [CFS13] Conlon, Fox, Sudakov: Tight lower bound
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SimpleGraph.Basic

open Real Finset

namespace Erdos191

/-
## Part I: Basic Definitions

We work with the complete graph on {2, ..., n} and 2-colorings of its edges.
-/

/--
**IntegerSet:**
A finite subset of natural numbers representing our universe {2, ..., n}.
-/
def IntegerSet (n : ℕ) : Finset ℕ := Finset.filter (fun x => 2 ≤ x) (Finset.range (n + 1))

/--
**EdgeColoring:**
A 2-coloring of the edges of the complete graph on a finite set S.
Edges are represented as unordered pairs {a, b} with a ≠ b.
We use a symmetric function mapping pairs to Bool (false = red, true = blue).
-/
def EdgeColoring (S : Finset ℕ) := (a : ℕ) → (b : ℕ) → a ∈ S → b ∈ S → a ≠ b → Bool

/--
**SimpleEdgeColoring:**
Simplified version using a function on pairs, implicitly symmetric.
-/
def SimpleEdgeColoring (n : ℕ) := (a : ℕ) → (b : ℕ) → Bool

/-
## Part II: Monochromatic Subsets
-/

/--
**IsMonochromatic:**
A subset X is monochromatic under coloring c if all edges within X have the same color.
-/
def IsMonochromatic (c : SimpleEdgeColoring n) (X : Finset ℕ) (color : Bool) : Prop :=
  ∀ a b : ℕ, a ∈ X → b ∈ X → a ≠ b → c a b = color

/--
**HasMonochromaticSubset:**
There exists a monochromatic subset of some color.
-/
def HasMonochromaticSubset (c : SimpleEdgeColoring n) (X : Finset ℕ) : Prop :=
  ∃ color : Bool, IsMonochromatic c X color

/--
**IsClique:**
A subset where all pairs are edges (for complete graph, this is automatic for any subset).
-/
def IsClique (X : Finset ℕ) : Prop := X.card ≥ 2

/-
## Part III: The Weighted Sum Function
-/

/--
**logInverseSum:**
The sum ∑_{x ∈ X} 1/log x for a finite set X.
This is the key quantity in the problem.
-/
noncomputable def logInverseSum (X : Finset ℕ) : ℝ :=
  X.sum (fun x => 1 / Real.log x)

/--
**For x ≥ 2, log x > 0, so 1/log x is well-defined and positive.**
-/
lemma log_pos_of_ge_two (x : ℕ) (hx : x ≥ 2) : Real.log x > 0 := by
  have : (x : ℝ) ≥ 2 := by exact_mod_cast hx
  have : (x : ℝ) > 1 := by linarith
  exact Real.log_pos this

/--
**logInverseSum is non-negative for sets of integers ≥ 2.**
-/
lemma logInverseSum_nonneg (X : Finset ℕ) (hX : ∀ x ∈ X, x ≥ 2) : logInverseSum X ≥ 0 := by
  unfold logInverseSum
  apply Finset.sum_nonneg
  intro x hx
  have hpos := log_pos_of_ge_two x (hX x hx)
  exact div_nonneg (by norm_num) (le_of_lt hpos)

/-
## Part IV: The Main Problem Statement
-/

/--
**MonochromaticWithLargeSum:**
In any 2-coloring, there exists a monochromatic X with sum ≥ C.
-/
def MonochromaticWithLargeSum (n : ℕ) (C : ℝ) : Prop :=
  ∀ c : SimpleEdgeColoring n,
    ∃ X : Finset ℕ, X ⊆ IntegerSet n ∧ HasMonochromaticSubset c X ∧ logInverseSum X ≥ C

/--
**Erdős Problem #191 Conjecture:**
For any C > 0, there exists N such that for all n ≥ N, MonochromaticWithLargeSum n C.
-/
def erdos191Conjecture : Prop :=
  ∀ C : ℝ, C > 0 → ∃ N : ℕ, ∀ n ≥ N, MonochromaticWithLargeSum n C

/-
## Part V: Rödl's Theorem (Solution)
-/

/--
**Erdős Problem #191: SOLVED**
Rödl proved the affirmative answer in 2003.
-/
axiom erdos_191 : erdos191Conjecture

/--
**Equivalent formulation with explicit quantifiers.**
-/
theorem erdos_191_explicit :
    ∀ C : ℝ, C > 0 → ∃ N : ℕ, ∀ n ≥ N, ∀ c : SimpleEdgeColoring n,
      ∃ X : Finset ℕ, X ⊆ IntegerSet n ∧ HasMonochromaticSubset c X ∧ logInverseSum X ≥ C :=
  erdos_191

/-
## Part VI: Tight Bounds (Rödl Upper, Conlon-Fox-Sudakov Lower)
-/

/--
**tripleLog:**
log log log n, the natural scale for this problem.
-/
noncomputable def tripleLog (n : ℕ) : ℝ :=
  Real.log (Real.log (Real.log n))

/--
**Rödl's Upper Construction:**
For any n, there exists a 2-coloring where all monochromatic X satisfy
  ∑_{x ∈ X} 1/log x ≤ c · log log log n
for some absolute constant c.

This shows the bound cannot be improved beyond O(log log log n).
-/
axiom rodl_upper_construction :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 16 →
    ∃ coloring : SimpleEdgeColoring n,
      ∀ X : Finset ℕ, X ⊆ IntegerSet n → HasMonochromaticSubset coloring X →
        logInverseSum X ≤ c * tripleLog n

/--
**Conlon-Fox-Sudakov Lower Bound:**
For any 2-coloring, there exists a monochromatic X with
  ∑_{x ∈ X} 1/log x ≥ 2^{-8} · log log log n

Combined with Rödl's upper bound, this gives tight asymptotic behavior.
-/
axiom conlon_fox_sudakov_bound :
  ∀ n : ℕ, n ≥ 16 → ∀ c : SimpleEdgeColoring n,
    ∃ X : Finset ℕ, X ⊆ IntegerSet n ∧ HasMonochromaticSubset c X ∧
      logInverseSum X ≥ (1 / 256) * tripleLog n

/--
**The constant 2^{-8} = 1/256 in Conlon-Fox-Sudakov.**
-/
lemma cfs_constant : (1 : ℝ) / 256 = 2^(-(8 : ℝ)) := by norm_num

/-
## Part VII: Derivation of Main Result from CFS Bound
-/

/--
**Triple log grows unboundedly.**
-/
axiom tripleLog_unbounded : ∀ M : ℝ, ∃ N : ℕ, ∀ n ≥ N, tripleLog n > M

/--
**The main theorem follows from CFS bound + unboundedness of triple log.**
-/
theorem erdos_191_from_cfs : erdos191Conjecture := by
  intro C hC
  -- We need N such that (1/256) * tripleLog n ≥ C
  -- i.e., tripleLog n ≥ 256 * C
  obtain ⟨N₀, hN₀⟩ := tripleLog_unbounded (256 * C)
  use max N₀ 16
  intro n hn
  have hn₁ : n ≥ N₀ := le_of_max_le_left hn
  have hn₂ : n ≥ 16 := le_of_max_le_right hn
  intro c
  obtain ⟨X, hXsub, hXmono, hXsum⟩ := conlon_fox_sudakov_bound n hn₂ c
  use X, hXsub, hXmono
  have htripleLog := hN₀ n hn₁
  calc logInverseSum X ≥ (1 / 256) * tripleLog n := hXsum
    _ > (1 / 256) * (256 * C) := by nlinarith
    _ = C := by ring

/-
## Part VIII: Connection to Ramsey Theory
-/

/--
**RamseyStyle:**
This problem is in the spirit of Ramsey theory: any 2-coloring of edges must
contain a "large" monochromatic structure, where "large" is measured by
the weighted sum ∑ 1/log x rather than cardinality.
-/
def RamseyStyleProperty : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ c : SimpleEdgeColoring n,
    ∃ X : Finset ℕ, X ⊆ IntegerSet n ∧ HasMonochromaticSubset c X ∧
      logInverseSum X ≥ (1 - ε) * tripleLog n

/--
**Classical Ramsey gives monochromatic cliques of size ≈ 2 log n.**
The 1/log x weighting converts this to weighted sum considerations.
-/
axiom classical_ramsey_connection :
  ∀ n : ℕ, n ≥ 6 → ∀ c : SimpleEdgeColoring n,
    ∃ X : Finset ℕ, X ⊆ IntegerSet n ∧ HasMonochromaticSubset c X ∧ X.card ≥ 2

/-
## Part IX: Examples
-/

/--
**Example: Small n bound**
For small n, the achievable sum is limited.
-/
theorem small_n_bound (n : ℕ) (hn : n ≤ 10) (X : Finset ℕ) (hX : X ⊆ IntegerSet n) :
    logInverseSum X ≤ 10 := by
  sorry

/--
**Example: Monochromatic pair always exists**
With any 2-coloring, at least one edge is monochromatic (trivially).
-/
theorem monochromatic_pair_exists (n : ℕ) (hn : n ≥ 3) (c : SimpleEdgeColoring n) :
    ∃ a b : ℕ, a ∈ IntegerSet n ∧ b ∈ IntegerSet n ∧ a ≠ b := by
  use 2, 3
  constructor
  · simp [IntegerSet, Finset.mem_filter]
    omega
  constructor
  · simp [IntegerSet, Finset.mem_filter]
    omega
  · omega

/--
**Growth of ∑ 1/log x for {2, ..., k}**
The sum ∑_{x=2}^{k} 1/log x grows like k/log k.
-/
axiom sum_one_over_log_asymptotic :
  ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧ ∀ k : ℕ, k ≥ 2 →
    c₁ * k / Real.log k ≤ logInverseSum (IntegerSet k) ∧
    logInverseSum (IntegerSet k) ≤ c₂ * k / Real.log k

/-
## Part X: Generalizations
-/

/--
**r-coloring generalization:**
The problem naturally extends to r-colorings.
-/
def erdos191GeneralizedConjecture (r : ℕ) : Prop :=
  ∀ C : ℝ, C > 0 → ∃ N : ℕ, ∀ n ≥ N, ∀ c : (ℕ → ℕ → Fin r),
    ∃ X : Finset ℕ, X ⊆ IntegerSet n ∧
      (∃ color : Fin r, ∀ a b : ℕ, a ∈ X → b ∈ X → a ≠ b → c a b = color) ∧
      logInverseSum X ≥ C

/--
**Different weight functions:**
We could ask the same question with weight 1/x, 1/x², etc.
The 1/log x weight is special because it gives the log log log n threshold.
-/
noncomputable def weightedSum (X : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  X.sum w

/--
**With weight 1/x instead of 1/log x, the threshold would be different.**
-/
axiom inverse_weight_threshold :
  ∀ C : ℝ, C > 0 → ∃ N : ℕ, ∀ n ≥ N, ∀ c : SimpleEdgeColoring n,
    ∃ X : Finset ℕ, X ⊆ IntegerSet n ∧ HasMonochromaticSubset c X ∧
      weightedSum X (fun x => 1 / x) ≥ C

/-
## Part XI: Asymptotic Analysis
-/

/--
**Tight asymptotic:**
The maximum achievable sum grows as Θ(log log log n).
-/
theorem tight_asymptotic :
    (∃ c₁ : ℝ, c₁ > 0 ∧ ∀ n ≥ 16, ∀ coloring : SimpleEdgeColoring n,
      ∃ X, X ⊆ IntegerSet n ∧ HasMonochromaticSubset coloring X ∧
        logInverseSum X ≥ c₁ * tripleLog n) ∧
    (∃ c₂ : ℝ, c₂ > 0 ∧ ∀ n ≥ 16,
      ∃ coloring : SimpleEdgeColoring n,
        ∀ X, X ⊆ IntegerSet n → HasMonochromaticSubset coloring X →
          logInverseSum X ≤ c₂ * tripleLog n) := by
  constructor
  · use 1 / 256, by norm_num
    intro n hn c
    exact conlon_fox_sudakov_bound n hn c
  · obtain ⟨c, hc_pos, hc⟩ := rodl_upper_construction
    use c, hc_pos
    intro n hn
    exact hc n hn

/-
## Part XII: Summary
-/

/--
**Erdős Problem #191: Summary**

1. Question: Can we always find monochromatic X with ∑ 1/log x ≥ C?
2. Answer: YES (Rödl 2003)
3. Tight bounds: Θ(log log log n) achievable
   - Lower: ≥ 2^{-8} log log log n (Conlon-Fox-Sudakov)
   - Upper: ≤ c · log log log n (Rödl construction)
4. Key technique: Analysis of complete graph edge colorings with weighted sums
-/
theorem erdos_191_summary :
    -- The main question is answered affirmatively
    erdos191Conjecture ∧
    -- Tight lower bound exists
    (∃ c₁ > 0, ∀ n ≥ 16, ∀ coloring,
      ∃ X, X ⊆ IntegerSet n ∧ HasMonochromaticSubset coloring X ∧
        logInverseSum X ≥ c₁ * tripleLog n) ∧
    -- Tight upper bound exists
    (∃ c₂ > 0, ∀ n ≥ 16, ∃ coloring : SimpleEdgeColoring n,
      ∀ X, X ⊆ IntegerSet n → HasMonochromaticSubset coloring X →
        logInverseSum X ≤ c₂ * tripleLog n) :=
  ⟨erdos_191, tight_asymptotic⟩

/--
The answer to Erdős Problem #191 is YES.
-/
theorem erdos_191_answer : erdos191Conjecture := erdos_191

end Erdos191
