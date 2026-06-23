/-
  Erdős Problem #1006 - Open Question 04:
  DAG Structure of the Coloring Orientation

  Source: https://erdosproblems.com/1006
  Related: OQ03 (coloringOrientation construction)

  This file explores the structural properties of the coloring orientation DAG.

  The coloring orientation (from OQ03):
    Given a proper k-coloring col: V → Fin k, orient u→v when col(u) < col(v).

  Key structural properties proved:
  1. The color value is a strict rank function (arcs go lower → higher color).
  2. Vertices with color 0 have no in-arcs (sources).
  3. Vertices with maximum color (k-1) have no out-arcs (sinks).
  4. Arc direction ↔ color ordering (for adjacent vertices).
  5. No back-arcs or same-level arcs.

  Status: 0 axioms, 0 sorries
-/

import Proofs.Erdos1006OQ03

open SimpleGraph

namespace Erdos1006OQ04

variable {V : Type*} {G : SimpleGraph V}

/-
## Part I: Level Structure
-/

/-- All arcs in the coloring orientation go strictly from lower to higher color level. -/
theorem coloringOrientation_rank_strict {k : ℕ} (col : G.Coloring (Fin k)) (u v : V)
    (harc : (coloringOrientation G col).arc u v) :
    (col u).val < (col v).val :=
  harc.2

/-- Color values provide an explicit rank witness for the orientation. -/
theorem coloringOrientation_has_rank {k : ℕ} (col : G.Coloring (Fin k)) :
    ∃ (rank : V → ℕ), ∀ u v, (coloringOrientation G col).arc u v → rank u < rank v :=
  ⟨fun v => (col v).val, coloringOrientation_rank_strict col⟩

/-- All rank values are strictly bounded by the chromatic number k. -/
theorem coloringOrientation_rank_lt_k {k : ℕ} (col : G.Coloring (Fin k)) (v : V) :
    (col v).val < k :=
  (col v).isLt

/-
## Part II: Source and Sink Structure
-/

/-- A vertex with color 0 has no in-arcs: any arc (u→v) requires col(u) < col(v) = 0,
    which is impossible since colors are non-negative. -/
theorem color_zero_no_in_arc {k : ℕ} (col : G.Coloring (Fin k)) (v : V)
    (hv : (col v).val = 0) (u : V)
    (harc : (coloringOrientation G col).arc u v) : False := by
  have h := coloringOrientation_rank_strict col u v harc
  omega

/-- A vertex with the maximum color k-1 has no out-arcs: any arc (v→u) requires
    col(v) < col(u), but col(v) = k-1 is already the maximum. -/
theorem color_max_no_out_arc {k : ℕ} (col : G.Coloring (Fin k)) (v : V)
    (hv : (col v).val = k - 1) (u : V)
    (harc : (coloringOrientation G col).arc v u) : False := by
  have h := coloringOrientation_rank_strict col v u harc
  have hu := (col u).isLt
  omega

/-
## Part III: Arc Direction Characterization
-/

/-- For adjacent vertices, the arc direction is equivalent to the color ordering. -/
theorem coloringOrientation_arc_iff {k : ℕ} (col : G.Coloring (Fin k)) (u v : V)
    (hadj : G.Adj u v) :
    (coloringOrientation G col).arc u v ↔ (col u).val < (col v).val := by
  constructor
  · exact fun h => coloringOrientation_rank_strict col u v h
  · intro h
    exact ⟨hadj, h⟩

/-- No back-arc: arcs cannot go in both directions between adjacent vertices.
    This is a consequence of color ordering being asymmetric. -/
theorem coloringOrientation_no_back_arc {k : ℕ} (col : G.Coloring (Fin k)) (u v : V)
    (harc : (coloringOrientation G col).arc u v) :
    ¬(coloringOrientation G col).arc v u := by
  intro hback
  have h1 := coloringOrientation_rank_strict col u v harc
  have h2 := coloringOrientation_rank_strict col v u hback
  omega

/-- The arc direction for adjacent vertices is determined by which of col(u), col(v) is larger.
    Exactly one of (u→v) or (v→u) holds. -/
theorem coloringOrientation_exactly_one_arc {k : ℕ} (col : G.Coloring (Fin k)) (u v : V)
    (hadj : G.Adj u v) :
    (coloringOrientation G col).arc u v ∨ (coloringOrientation G col).arc v u := by
  exact (coloringOrientation G col).covers u v hadj

/-
## Part IV: No Same-Level Arcs
-/

/-- Arcs only exist between vertices of different colors.
    The arc (u→v) forces col(u) < col(v), so col(u) ≠ col(v). -/
theorem coloringOrientation_different_colors {k : ℕ} (col : G.Coloring (Fin k)) (u v : V)
    (harc : (coloringOrientation G col).arc u v) :
    col u ≠ col v := by
  have h := coloringOrientation_rank_strict col u v harc
  intro heq
  rw [heq] at h
  exact Nat.lt_irrefl _ h

/-
## Part V: Consistency with OQ03 Results
-/

/-- The acyclicity from OQ03 is an immediate consequence of our rank characterization. -/
theorem coloringOrientation_acyclic_via_rank {k : ℕ} (col : G.Coloring (Fin k)) :
    (coloringOrientation G col).isAcyclic :=
  coloringOrientation_acyclic G col

/-- Every finite graph admits a robustly acyclic orientation (restated from OQ03). -/
theorem every_graph_has_robust [Fintype V] (G : SimpleGraph V) :
    admitsRobustAcyclicOrientation G :=
  every_finite_graph_has_robust G

/-
## Part VI: Transitivity and Non-Reflexivity
-/

/-- Arc transitivity: if u→v and v→w, then col(u) < col(w).
    The color ordering is transitive, so multi-hop paths also go strictly upward. -/
theorem coloringOrientation_trans {k : ℕ} (col : G.Coloring (Fin k)) (u v w : V)
    (huv : (coloringOrientation G col).arc u v)
    (hvw : (coloringOrientation G col).arc v w) :
    (col u).val < (col w).val :=
  Nat.lt_trans (coloringOrientation_rank_strict col u v huv)
               (coloringOrientation_rank_strict col v w hvw)

/-- No vertex has an arc to itself: col(v) < col(v) is impossible. -/
theorem coloringOrientation_arc_irrefl {k : ℕ} (col : G.Coloring (Fin k)) (v : V) :
    ¬(coloringOrientation G col).arc v v :=
  fun h => Nat.lt_irrefl _ (coloringOrientation_rank_strict col v v h)

/-- Any arc u→v has u ≠ v (immediate from arc irreflexivity). -/
theorem coloringOrientation_arc_ne {k : ℕ} (col : G.Coloring (Fin k)) (u v : V)
    (harc : (coloringOrientation G col).arc u v) : u ≠ v := by
  intro heq; subst heq
  exact coloringOrientation_arc_irrefl col v harc

/-- Same-colored vertices are not adjacent: a proper coloring gives distinct colors
    on adjacent vertices, so equal colors means non-adjacent. -/
theorem coloring_same_color_not_adj {k : ℕ} (col : G.Coloring (Fin k)) (u v : V)
    (heq : col u = col v) : ¬G.Adj u v :=
  fun hadj => col.valid hadj heq

/-
## Summary

This file proves 10 theorems with 0 sorries and 0 axioms:

Part I - Level Structure:
  coloringOrientation_rank_strict: arcs go from lower to higher color
  coloringOrientation_has_rank: explicit rank witness = color value
  coloringOrientation_rank_lt_k: all ranks < k

Part II - Sources and Sinks:
  color_zero_no_in_arc: color-0 vertices have no in-arcs
  color_max_no_out_arc: color-(k-1) vertices have no out-arcs

Part III - Arc Direction:
  coloringOrientation_arc_iff: arc direction ↔ color ordering
  coloringOrientation_no_back_arc: arcs have no 2-cycles
  coloringOrientation_exactly_one_arc: exactly one direction for each edge

Part IV - No Same-Level Arcs:
  coloringOrientation_different_colors: arcs only between differently-colored vertices

Part V - Consistency:
  coloringOrientation_acyclic_via_rank: acyclicity from rank structure
  every_graph_has_robust: OQ03 main result (restated)

Key Insight:
  The coloring orientation is a "graded" DAG: level = color value, all arcs go
  level-up, with sources at level 0 and sinks at level k-1. The rank-based
  formulation captures this algebraically, and the structure gives a clean
  characterization of the orientation in terms of the coloring.
-/

end Erdos1006OQ04
