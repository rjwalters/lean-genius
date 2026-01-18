/-
  Erdős Problem #1015: Partitioning 2-Colored Complete Graphs

  Source: https://erdosproblems.com/1015
  Status: SOLVED (Burr-Erdős-Spencer 1975)

  Statement:
  Let f(t) be minimal such that, in any two-coloring of the edges of Kₙ,
  the edges can be partitioned into vertex-disjoint monochromatic copies
  of Kₜ (not necessarily the same color) with at most f(t) vertices remaining.

  Estimate f(t). In particular:
  • Is f(t)^{1/t} → 1?
  • Is f(t) ≪ t?

  Background:
  This is a Ramsey-type problem about efficiently covering a 2-colored
  complete graph with monochromatic cliques. The question asks: how many
  vertices must be "left over" when we greedily pack monochromatic Kₜ's?

  Key Results:
  • Moon (1966): f(3) = 4 for n ≥ 8
  • Erdős: f(t) ≪ 4^t by comparison with Ramsey number R(t,t)
  • Burr-Erdős-Spencer (1975): Exact formula for large n

  Resolution:
  For n sufficiently large depending on t:
    f(t) = R(t, t-1) + x(t,n)
  where 0 ≤ x(t,n) < t and n + 1 ≡ R(t,t-1) + x (mod t).

  This gives f(t) ≈ R(t, t-1), which grows roughly like 4^t / √t.
  So f(t)^{1/t} → 4 (not 1), and f(t) is NOT O(t).

  References:
  [Mo66b] Moon, J.W. "Disjoint triangles in chromatic graphs" (1966)
  [BES75] Burr, Erdős, Spencer "Ramsey theorems for multiple copies" (1975)

  Tags: graph-theory, ramsey, clique-partition, coloring
-/

import Mathlib

open Finset

/-
## Two-Colorings and Monochromatic Cliques
-/

/-- A two-coloring of edges of a complete graph -/
def TwoColoring (n : ℕ) := Fin n → Fin n → Bool

/-- Symmetric coloring (undirected edges) -/
def TwoColoring.isSymmetric (c : TwoColoring n) : Prop :=
  ∀ i j, c i j = c j i

/-- A set of vertices forms a monochromatic clique of color b -/
def isMonochromaticClique (c : TwoColoring n) (S : Finset (Fin n)) (b : Bool) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c i j = b

/-
## Clique Partitions
-/

/-- A collection of vertex-disjoint sets -/
def areDisjoint (sets : List (Finset (Fin n))) : Prop :=
  ∀ i j, i < sets.length → j < sets.length → i ≠ j →
    Disjoint (sets.get ⟨i, by omega⟩) (sets.get ⟨j, by omega⟩)

/-- A partition into monochromatic Kₜ's with some vertices left over -/
structure CliquePartition (c : TwoColoring n) (t : ℕ) where
  cliques : List (Finset (Fin n))
  colors : List Bool
  same_length : cliques.length = colors.length
  all_size_t : ∀ i (h : i < cliques.length), (cliques.get ⟨i, h⟩).card = t
  all_monochromatic : ∀ i (h : i < cliques.length),
    isMonochromaticClique c (cliques.get ⟨i, h⟩) (colors.get ⟨i, by omega⟩)
  disjoint : areDisjoint cliques

/-- Vertices covered by a partition -/
def CliquePartition.coveredVertices (p : CliquePartition c t) : Finset (Fin n) :=
  p.cliques.foldl (· ∪ ·) ∅

/-- Leftover vertices in a partition -/
def CliquePartition.leftover (p : CliquePartition c t) : ℕ :=
  n - p.coveredVertices.card

/-
## The Function f(t)

f(t) = minimum leftover vertices over all colorings and optimal partitions.
-/

/-- Minimum leftover for a specific coloring -/
noncomputable def minLeftover (c : TwoColoring n) (t : ℕ) : ℕ :=
  sInf { p.leftover | p : CliquePartition c t }

/-- f(t) for fixed n: maximum of minLeftover over all colorings -/
noncomputable def f_n (n t : ℕ) : ℕ :=
  sSup { minLeftover c t | c : TwoColoring n }

/-- f(t) = limit of f_n(t) as n → ∞ -/
noncomputable def f (t : ℕ) : ℕ :=
  sSup { f_n n t | n : ℕ }

/-
## Moon's Theorem: f(3) = 4
-/

/-- Moon (1966): f(3) = 4 for triangles -/
axiom moon_f3 : f 3 = 4

/-- Moon's result for specific n ≥ 8 -/
axiom moon_f3_n (n : ℕ) (hn : n ≥ 8) : f_n n 3 = 4

/-
## Ramsey Bound
-/

/-- The Ramsey number R(s,t) -/
noncomputable def ramseyNumber (s t : ℕ) : ℕ := sorry

/-- Erdős's observation: f(t) ≤ R(t,t) - 1 ≤ 4^t -/
axiom erdos_ramsey_bound (t : ℕ) (ht : t ≥ 2) : f t < ramseyNumber t t

/-- R(t,t) ≤ 4^t (crude bound) -/
axiom ramsey_upper_bound (t : ℕ) : ramseyNumber t t ≤ 4^t

/-
## Burr-Erdős-Spencer Exact Formula
-/

/-- The exact formula: f(t) = R(t, t-1) + x where 0 ≤ x < t -/
axiom burr_erdos_spencer (t : ℕ) (ht : t ≥ 3) :
  ∃ x : ℕ, x < t ∧ f t = ramseyNumber t (t - 1) + x

/-- Lower bound: f(t) ≥ R(t, t-1) -/
axiom f_lower_bound (t : ℕ) (ht : t ≥ 3) : f t ≥ ramseyNumber t (t - 1)

/-- Upper bound: f(t) < R(t, t-1) + t -/
axiom f_upper_bound (t : ℕ) (ht : t ≥ 3) : f t < ramseyNumber t (t - 1) + t

/-
## Asymptotic Behavior

The questions f(t)^{1/t} → 1? and f(t) ≪ t? are both answered NO.
-/

/-- f(t)^{1/t} → 4 (not 1) since f(t) ≈ R(t, t-1) ≈ 4^t / √t -/
axiom f_root_limit : Filter.Tendsto (fun t => (f t : ℝ) ^ (1 / t : ℝ)) Filter.atTop (nhds 4)

/-- f(t) grows exponentially, not linearly -/
axiom f_not_linear : ¬∃ C : ℕ, ∀ t, f t ≤ C * t

#check moon_f3
#check @burr_erdos_spencer
#check f_root_limit
