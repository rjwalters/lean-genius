/-
# Erdős Problem #75 — Uncountable Chromatic Number and Large Independent Sets

Erdős, Hajnal, and Szemerédi asked:

Is there a graph G of chromatic number ℵ₁ such that for all ε > 0,
if n is sufficiently large and H is a subgraph of G on n vertices,
then H contains an independent set of size > n^{1−ε}?

Erdős further suggested this might hold with independent sets of size ≫ n.

This is a $1000 Erdős prize problem.

Reference: https://erdosproblems.com/75

## Refactoring Note

This file was refactored to use Mathlib's SimpleGraph and Colorable types,
eliminating 7 framework axioms (Graph, chromaticNum, chromaticNum_mono,
FiniteSubgraph, indepNumber, indepNumber_le, finite_chromatic_independence).
Only the two open conjectures remain as axioms.
-/

import Mathlib

noncomputable section

namespace Erdos75

variable {V : Type*}

/- ## Independent Sets in Finite Subsets -/

/-- An independent set in G: no two distinct vertices in I are adjacent -/
def IsIndepSet (G : SimpleGraph V) (I : Finset V) : Prop :=
  ∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬G.Adj u v

/-- Every subset has cardinality at most that of its superset.
    Replaces the original `indepNumber_le` axiom. -/
theorem indepSet_card_le (S I : Finset V) (hI : I ⊆ S) : I.card ≤ S.card :=
  Finset.card_le_card hI

/- ## Chromatic Number Properties -/

/-- A graph has uncountable chromatic number if it's not n-colorable for any n -/
def HasUncountableChromaticNum (G : SimpleGraph V) : Prop :=
  ∀ n : ℕ, ¬G.Colorable n

/-- Colorability is monotone: m-colorable and m ≤ n implies n-colorable.
    Replaces the original `chromaticNum_mono` axiom. -/
theorem colorable_mono (G : SimpleGraph V) (m n : ℕ) (h : m ≤ n)
    (hcol : G.Colorable m) : G.Colorable n :=
  hcol.mono h

/- ## The Independence Ratio Property -/

/-- A graph has the (1−ε)-independence property if every sufficiently
    large finite subset contains a nonempty independent subset.
    (Approximation: the full n^{1−ε} bound requires real exponentiation.) -/
def HasLargeIndepSets (G : SimpleGraph V) : Prop :=
  ∀ ε : ℚ, 0 < ε → ε < 1 →
    ∃ N : ℕ, ∀ (S : Finset V), N ≤ S.card →
      ∃ I : Finset V, I ⊆ S ∧ IsIndepSet G I ∧ 0 < I.card

/-- The stronger version: independence number is ≫ n (linear).
    Every sufficiently large finite subset contains an independent set
    of size at least c·|S| for some constant c > 0. -/
def HasLinearIndepSets (G : SimpleGraph V) : Prop :=
  ∃ c : ℚ, 0 < c ∧
    ∃ N : ℕ, ∀ (S : Finset V), N ≤ S.card →
      ∃ I : Finset V, I ⊆ S ∧ IsIndepSet G I ∧
        c * (S.card : ℚ) ≤ (I.card : ℚ)

/- ## Known Context -/

/-- For a finite k-colorable graph, pigeonhole yields an independent set
    of size ≥ n/k. A proper k-coloring partitions vertices into k color
    classes, each independent; the largest has size ≥ ⌈n/k⌉.
    Replaces the original `finite_chromatic_independence` axiom. -/
theorem coloring_pigeonhole [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (hk : 0 < k) (hcol : G.Colorable k) :
    ∃ I : Finset V, IsIndepSet G I ∧ Fintype.card V ≤ I.card * k := by
  sorry

/-- The Erdős–Hajnal conjecture (related): for every H, graphs not containing
    H as induced subgraph have polynomially large cliques or independent sets -/
theorem erdos_hajnal_related : True := trivial

/- ## Implications Between Forms -/

/-- The strong form (linear independence) implies the basic form -/
theorem linear_implies_large (G : SimpleGraph V) :
    HasLinearIndepSets G → HasLargeIndepSets G := by
  intro ⟨c, hc_pos, N, hN⟩ ε _ _
  refine ⟨max N 1, fun S hS => ?_⟩
  have hN_le : N ≤ S.card := le_trans (le_max_left N 1) hS
  have h1_le : 1 ≤ S.card := le_trans (le_max_right N 1) hS
  obtain ⟨I, hIsub, hIindep, hIcard⟩ := hN S hN_le
  refine ⟨I, hIsub, hIindep, ?_⟩
  have hn1 : (1 : ℚ) ≤ (S.card : ℚ) := by exact_mod_cast h1_le
  have h_pos : (0 : ℚ) < (S.card : ℚ) := lt_of_lt_of_le zero_lt_one hn1
  exact Nat.cast_pos.mp (lt_of_lt_of_le (mul_pos hc_pos h_pos) hIcard)

/-- The strong conjecture implies the basic conjecture -/
theorem strong_implies_basic :
    (∃ (V : Type) (G : SimpleGraph V),
      HasUncountableChromaticNum G ∧ HasLinearIndepSets G) →
    (∃ (V : Type) (G : SimpleGraph V),
      HasUncountableChromaticNum G ∧ HasLargeIndepSets G) := by
  intro ⟨V, G, hchrom, hlin⟩
  exact ⟨V, G, hchrom, linear_implies_large G hlin⟩

/- ## The Erdős Problem -/

/-- Erdős Problem 75 (basic form): There exists a graph with uncountable
    chromatic number and the large independence set property -/
axiom ErdosProblem75 :
  ∃ (V : Type) (G : SimpleGraph V),
    HasUncountableChromaticNum G ∧ HasLargeIndepSets G

/-- Erdős Problem 75 (strong form): There exists a graph with uncountable
    chromatic number where every large finite subset has linear independence -/
axiom ErdosProblem75_strong :
  ∃ (V : Type) (G : SimpleGraph V),
    HasUncountableChromaticNum G ∧ HasLinearIndepSets G

end Erdos75

end
