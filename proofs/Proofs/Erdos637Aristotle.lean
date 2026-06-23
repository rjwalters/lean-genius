/-
  Aristotle targets for Erdős Problem #637
  Routine supporting lemmas for automated proof search.
  See Erdos637Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main results (Bukh-Sudakov, JKLY) or deep Ramsey bounds
  - Known results provable from Mathlib (image cardinality, degree bounds)
  - Clean theorem statements with no definition sorries
  - No axioms

  The main file formalizes: If G is a Ramsey graph (small clique/independence
  numbers), it must contain an induced subgraph with many distinct degrees.
-/
import Mathlib

namespace Erdos637Aristotle

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/- ## Definitions (mirrored from Erdos637Problem.lean) -/

/-- The degree of a vertex in a graph. -/
noncomputable def vertexDegree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  G.degree v

/-- The set of distinct degrees in a graph. -/
noncomputable def distinctDegrees (G : SimpleGraph V) [DecidableRel G.Adj] : Finset ℕ :=
  Finset.image (vertexDegree G) Finset.univ

/-- Number of distinct degrees in G. -/
noncomputable def numDistinctDegrees (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (distinctDegrees G).card

/-- A graph is k-regular if all degrees equal k. -/
def IsRegular (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : Prop :=
  ∀ v : V, vertexDegree G v = k

/- ## Routine Lemmas -/

-- Regular graphs
/-- Regular graphs have exactly 1 distinct degree. -/
theorem regular_one_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (h : IsRegular G k) [Nonempty V] :
    numDistinctDegrees G = 1 := by
  unfold numDistinctDegrees distinctDegrees
  have : Finset.image (vertexDegree G) Finset.univ = {k} := by
    ext d; simp [Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨v, _, rfl⟩; exact h v
    · intro hd; exact ⟨Classical.arbitrary V, Finset.mem_univ _, hd ▸ (h _).symm⟩
  rw [this, Finset.card_singleton]

-- Degree bounds
/-- The number of distinct degrees is at most n (number of vertices). -/
theorem numDistinctDegrees_le_card (G : SimpleGraph V) [DecidableRel G.Adj] :
    numDistinctDegrees G ≤ Fintype.card V := by
  unfold numDistinctDegrees distinctDegrees
  calc (Finset.image (vertexDegree G) Finset.univ).card
      ≤ Finset.univ.card := Finset.card_image_le
    _ = Fintype.card V := Finset.card_univ

/-- The number of distinct degrees is at most n (the max possible degree is n-1). -/
theorem numDistinctDegrees_le_card' (G : SimpleGraph V) [DecidableRel G.Adj] :
    numDistinctDegrees G ≤ Fintype.card V :=
  numDistinctDegrees_le_card G

/-- Every vertex has degree at most n-1. -/
theorem degree_lt_card (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    vertexDegree G v < Fintype.card V := by
  unfold vertexDegree
  exact G.degree_lt_card v

/-- If the graph has at least one vertex, it has at least one distinct degree. -/
theorem numDistinctDegrees_pos (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] :
    numDistinctDegrees G ≥ 1 := by
  unfold numDistinctDegrees distinctDegrees
  have : (Finset.image (vertexDegree G) Finset.univ).Nonempty :=
    Finset.Nonempty.image (Finset.univ_nonempty) _
  exact Finset.Nonempty.card_pos this

-- Induced subgraph degrees
/-- An induced subgraph on a vertex set S. -/
def inducedSubgraph (G : SimpleGraph V) (S : Finset V) : SimpleGraph S where
  Adj := fun u v => G.Adj u.val v.val
  symm := fun _ _ h => G.symm h
  loopless := fun v => G.loopless v.val

/-- Degrees in an induced subgraph are bounded by degrees in the full graph. -/
theorem induced_degree_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : S) [DecidableRel (inducedSubgraph G S).Adj] :
    (inducedSubgraph G S).degree v ≤ G.degree v.val := by
  simp only [SimpleGraph.degree]
  -- Map induced neighbors injectively into full graph neighbors
  calc ((inducedSubgraph G S).neighborFinset v).card
      = (((inducedSubgraph G S).neighborFinset v).image Subtype.val).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (G.neighborFinset v.val).card := by
        apply Finset.card_le_card
        intro u hu
        rw [Finset.mem_image] at hu
        obtain ⟨w, hw, rfl⟩ := hu
        rw [SimpleGraph.mem_neighborFinset] at hw ⊢
        exact hw

-- The empty graph
/-- The empty graph (no edges) is 0-regular. -/
theorem bot_regular : IsRegular (⊥ : SimpleGraph V) (DecidableRel := Classical.decRel _) 0 := by
  intro v; unfold vertexDegree
  have : (⊥ : SimpleGraph V).neighborFinset v = ∅ := by
    ext w; simp [SimpleGraph.mem_neighborFinset]
  simp [SimpleGraph.degree, this]

/-- The complete graph on n vertices is (n-1)-regular. -/
theorem top_regular [Nonempty V] :
    IsRegular (⊤ : SimpleGraph V) (DecidableRel := Classical.decRel _) (Fintype.card V - 1) := by
  intro v; unfold vertexDegree
  have : (⊤ : SimpleGraph V).neighborFinset v = Finset.univ.erase v := by
    ext w; simp [SimpleGraph.mem_neighborFinset, Finset.mem_erase, ne_comm]
  simp [SimpleGraph.degree, this, Finset.card_erase_of_mem (Finset.mem_univ v)]

end Erdos637Aristotle
