/-
  Aristotle targets for Erdős Problem #637
  Routine supporting lemmas for automated proof search.
  See Erdos637Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main results (Bukh-Sudakov, JKLY — cited research results)
  - NOT the open optimality conjecture
  - Routine algebraic/set-theoretic consequences of definitions

  Included targets (1):
  - regular_one_degree: a k-regular graph has exactly 1 distinct degree
-/
import Mathlib

namespace Erdos637ProblemAristotle

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def vertexDegree (G : SimpleGraph V) (v : V) : ℕ :=
  (G.neighborFinset v).card

noncomputable def distinctDegrees (G : SimpleGraph V) : Finset ℕ :=
  Finset.image (vertexDegree G) Finset.univ

noncomputable def numDistinctDegrees (G : SimpleGraph V) : ℕ :=
  (distinctDegrees G).card

def IsRegular (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ v : V, vertexDegree G v = k

-- Routine: a k-regular graph has exactly 1 distinct degree.
-- All degrees equal k, so the image of vertexDegree over all vertices is {k}.
theorem regular_one_degree (G : SimpleGraph V) (k : ℕ) [Nonempty V] (h : IsRegular G k) :
    numDistinctDegrees G = 1 := by
  sorry

end Erdos637ProblemAristotle
