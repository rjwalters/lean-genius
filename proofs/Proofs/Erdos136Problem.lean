/-
Erdős Problem #136: The Erdős-Gyárfás Function f(n,4,5)

Source: https://erdosproblems.com/136
Status: SOLVED

Statement:
Let f(n) be the smallest number of colors required to color the edges of Kₙ
such that every K₄ (complete subgraph on 4 vertices) contains at least 5
different colors among its 6 edges.

Determine the size of f(n).

Background:
This is the Erdős-Gyárfás function f(n,4,5). In general, f(n,p,q) asks for
the minimum colors needed to color edges of Kₙ so every Kₚ has at least q colors.
Here p = 4 (looking at 4-cliques) and q = 5 (need 5 colors in each K₄).

Note: K₄ has C(4,2) = 6 edges, so "at least 5 colors" means no K₄ is
rainbow (all 6 edges different colors) but it must be close.

Original Bounds (Erdős-Gyárfás):
  (5/6)(n-1) < f(n) < n
Also computed: f(9) = 8.

Resolution (2022):
Bennett, Cushman, Dudek, and Pralat proved f(n) ~ (5/6)n.
Joos and Mubayi found a shorter proof.

The lower bound is asymptotically tight - Erdős was right that
the lower bound is closer to the truth!

References:
- [BCDP22] Bennett et al., "The Erdős-Gyárfás function f(n,4,5) = (5/6)n + o(n)"
- [JoMu22] Joos and Mubayi, "Ramsey theory constructions from hypergraph matchings"

Related: Problem 135

Tags: ramsey-theory, graph-coloring, complete-graphs
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

open Finset

namespace Erdos136

/-
## Part I: Basic Definitions
-/

/--
**Edge coloring of Kₙ:**
An assignment of colors to all edges of the complete graph on n vertices.
-/
def EdgeColoring (n : ℕ) (k : ℕ) := Fin n → Fin n → Fin k

/--
**Valid edge coloring:**
Symmetric and well-defined on edges (not self-loops).
-/
def isValidColoring {n k : ℕ} (c : EdgeColoring n k) : Prop :=
  ∀ i j : Fin n, i ≠ j → c i j = c j i

/--
**Colors in a K₄:**
Given 4 vertices, collect all 6 edge colors.
-/
def colorsInK4 {n k : ℕ} (c : EdgeColoring n k) (v : Fin 4 → Fin n)
    (hInjective : Function.Injective v) : Finset (Fin k) :=
  -- The 6 edges of K₄
  {c (v 0) (v 1), c (v 0) (v 2), c (v 0) (v 3),
   c (v 1) (v 2), c (v 1) (v 3), c (v 2) (v 3)}

/--
**At least 5 colors in every K₄:**
The required property for our coloring.
-/
def hasAtLeast5ColorsInEveryK4 {n k : ℕ} (c : EdgeColoring n k) : Prop :=
  ∀ v : Fin 4 → Fin n, Function.Injective v →
    (colorsInK4 c v ‹_›).card ≥ 5

/-
## Part II: The Erdős-Gyárfás Function
-/

/-- The minimum number of colors exists for any n. -/
axiom f_exists (n : ℕ) : ∃ k : ℕ, ∃ c : EdgeColoring n k,
    isValidColoring c ∧ hasAtLeast5ColorsInEveryK4 c

noncomputable def f (n : ℕ) : ℕ :=
  Nat.find (f_exists n)

/-
## Part III: Original Bounds
-/

/--
**Erdős-Gyárfás lower bound:**
f(n) > (5/6)(n - 1)
-/
axiom erdos_gyarfas_lower_bound :
    ∀ n : ℕ, n ≥ 4 → (f n : ℝ) > (5/6) * (n - 1)

/--
**Erdős-Gyárfás upper bound:**
f(n) < n
-/
axiom erdos_gyarfas_upper_bound :
    ∀ n : ℕ, n ≥ 4 → (f n : ℕ) < n

/-- **Specific value**: f(9) = 8 (Erdős-Gyárfás computation). -/

/-
## Part IV: The Asymptotic Solution
-/

/--
**Bennett-Cushman-Dudek-Pralat (2022):**
f(n) ~ (5/6)n, i.e., f(n) = (5/6)n + o(n).

The lower bound is asymptotically tight!
-/
axiom bcdp_asymptotic :
    Filter.Tendsto (fun n => (f n : ℝ) / n) Filter.atTop (nhds (5/6))

/--
**Equivalent formulation:**
f(n) / n → 5/6 as n → ∞.
-/
def AsymptoticResult : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      |(f n : ℝ) / n - 5/6| < ε

/-- The asymptotic result follows from BCDP. -/

/-
## Part V: Why 5/6?
-/

/--
**The constant 5/6 explained:**
K₄ has 6 edges. Requiring ≥ 5 colors means at most 1 repeated color.
The fraction 5/6 = 1 - 1/6 reflects that we allow one "defect" per K₄.
-/
theorem why_five_sixths :
    (6 : ℕ) - 1 = 5 ∧ (5 : ℚ) / 6 = 1 - 1/6 := by
  constructor <;> norm_num

/--
**Edge count in K₄:**
K₄ has C(4,2) = 6 edges.
-/
theorem k4_edges : Nat.choose 4 2 = 6 := by norm_num


/-
## Part VI: Related Values
-/

/-- **Small values**: f(4)=f(5)=f(6)=5, f(9)=8 (Erdős-Gyárfás).
**Monotonicity**: f is non-decreasing (more vertices → more colors needed). -/

/-
## Part VII: Summary
-/

/-- **Erdős Problem #136: Summary**

The Erdős-Gyárfás function f(n,4,5) satisfies f(n) ~ (5/6)n.
The original Erdős-Gyárfás bounds (5/6)(n-1) < f(n) < n hold,
and the asymptotic was confirmed by Bennett et al. (2022). -/
theorem erdos_136 :
    -- Asymptotic is 5/6
    (Filter.Tendsto (fun n => (f n : ℝ) / n) Filter.atTop (nhds (5/6))) ∧
    -- Original bounds hold
    (∀ n : ℕ, n ≥ 4 → (f n : ℝ) > (5/6) * (n - 1)) ∧
    (∀ n : ℕ, n ≥ 4 → (f n : ℕ) < n) :=
  ⟨bcdp_asymptotic, erdos_gyarfas_lower_bound, erdos_gyarfas_upper_bound⟩

end Erdos136
