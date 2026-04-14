/-
  Aristotle targets for Erdos637Problem
  Routine supporting lemmas for automated proof search.
  See Erdos637Problem.lean for the main formalization.

  Main file: Erdős Problem #637 — Distinct Degrees in Induced Subgraphs
  (Bukh-Sudakov 2007, JKLY 2020)

  The lemmas here are routine facts about degree sequences,
  NOT the main research results (those require Bukh-Sudakov / JKLY arguments).
-/
import Mathlib

namespace Erdos637

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The degree of a vertex in a graph. -/
noncomputable def vertexDegree (G : SimpleGraph V) (v : V) : ℕ :=
  (G.neighborFinset v).card

/-- The set of distinct degrees in a graph. -/
noncomputable def distinctDegrees (G : SimpleGraph V) : Finset ℕ :=
  Finset.image (vertexDegree G) Finset.univ

/-- Number of distinct degrees in G. -/
noncomputable def numDistinctDegrees (G : SimpleGraph V) : ℕ :=
  (distinctDegrees G).card

/-- A graph is k-regular if all vertices have degree k. -/
def IsRegular (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ v : V, vertexDegree G v = k

/-- Regular graphs have exactly 1 distinct degree. -/
lemma regular_one_degree (G : SimpleGraph V) (k : ℕ) (h : IsRegular G k) :
    numDistinctDegrees G = 1 := by sorry

end Erdos637
