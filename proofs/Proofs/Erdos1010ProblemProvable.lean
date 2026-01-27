/-
  Erdős Problem #1010: Triangle Count Beyond Turán Threshold

  Source: https://erdosproblems.com/1010
  Status: SOLVED (Lovász-Simonovits 1976, Nikiforov-Khadzhiivanov 1981)

  Statement:
  Let t < ⌊n/2⌋. Does every graph on n vertices with ⌊n²/4⌋ + t edges
  contain at least t · ⌊n/2⌋ triangles?

  Background:
  Turán's theorem (1941) established that the maximum number of edges in a
  triangle-free graph on n vertices is ⌊n²/4⌋, achieved by the complete
  bipartite graph K_{⌊n/2⌋, ⌈n/2⌉}.

  Rademacher (unpublished, attributed by Erdős) proved the first supersaturation
  result: every graph on n vertices with ⌊n²/4⌋ + 1 edges contains at least
  ⌊n/2⌋ triangles.

  Erdős [Er62d] extended this to show the result holds for t < cn for some
  constant c > 0. He conjectured the full result for all t < ⌊n/2⌋.

  Resolution:
  The conjecture is TRUE. Proved independently by:
  • Lovász and Simonovits (1976) - "On the number of complete subgraphs of a graph"
  • Nikiforov and Khadzhiivanov (1981) - C. R. Acad. Bulgare Sci.

  The Lovász-Simonovits paper developed the powerful "stability method" which
  has become fundamental in extremal graph theory.

  References:
  [Er62d] Erdős, P. "On a theorem of Rademacher-Turán" Illinois J. Math. (1962)
  [LoSi76] Lovász, L. and Simonovits, M. "On the number of complete subgraphs"
  [NiKh81] Nikiforov, V.S. and Khadzhiivanov, N.G. C. R. Acad. Bulgare Sci.

  Tags: graph-theory, extremal, triangles, turán, supersaturation
-/

import Mathlib

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-
## Turán Threshold

The Turán number ex(n, K₃) = ⌊n²/4⌋ is the maximum edges in a triangle-free graph.
-/

/-- The Turán threshold: maximum edges in a triangle-free graph on n vertices -/
def turanThreshold (n : ℕ) : ℕ := n^2 / 4

/-- Count of triangles in a graph (as a set of 3-cliques) -/
def triangleCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.filter (fun s : Finset V =>
    s.card = 3 ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → G.Adj x y)).card

/-
## Rademacher's Theorem (Base Case)

Every graph exceeding the Turán threshold by 1 edge has at least ⌊n/2⌋ triangles.
-/

/-- Rademacher's theorem: one edge over Turán forces ⌊n/2⌋ triangles -/
theorem rademacher_triangle_count (G : SimpleGraph V) [DecidableRel G.Adj] :
  G.edgeFinset.card = turanThreshold (Fintype.card V) + 1 →
  triangleCount G ≥ Fintype.card V / 2 := by sorry

/-
## Erdős-Lovász-Simonovits Theorem (Main Result)

For t < ⌊n/2⌋, exceeding the Turán threshold by t edges forces at least
t · ⌊n/2⌋ triangles. This is a "supersaturation" phenomenon.
-/

/-- The main theorem (Erdős Problem #1010):
    t edges over Turán threshold force at least t · ⌊n/2⌋ triangles -/
theorem erdos_1010_supersaturation (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ) :
  t < Fintype.card V / 2 →
  G.edgeFinset.card = turanThreshold (Fintype.card V) + t →
  triangleCount G ≥ t * (Fintype.card V / 2) := by sorry

/-
## Corollaries and Special Cases
-/

/-- Corollary: Any graph with more than ⌊n²/4⌋ edges has a triangle -/
theorem turán_triangle_existence (G : SimpleGraph V) [DecidableRel G.Adj] :
  G.edgeFinset.card > turanThreshold (Fintype.card V) →
  triangleCount G ≥ 1 := by
  intro h
  -- When t = 1 and n ≥ 2, we get at least 1 · ⌊n/2⌋ ≥ 1 triangle
  sorry

/-- The bound t · ⌊n/2⌋ is tight: Turán graph with t additional edges
    achieves exactly this many triangles when edges added optimally -/
theorem erdos_1010_tight (n t : ℕ) :
  t < n / 2 →
  ∃ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V = n ∧
    G.edgeFinset.card = turanThreshold n + t ∧
    triangleCount G = t * (n / 2) := by sorry

#check @erdos_1010_supersaturation
#check @rademacher_triangle_count
