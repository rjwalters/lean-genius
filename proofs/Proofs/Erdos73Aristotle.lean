/-
  Aristotle targets for Erdős Problem #73
  Routine supporting lemmas for automated proof search.
  See Erdos73Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT Reed's theorem (axiomatized deep result)
  - Routine graph-theoretic facts: K₃ properties, bipartiteness
  - Constructive examples: K₃ independence number, K₃ almost-bipartite
  - No axioms, no definition sorries, no open conjectures
  - Use only block comments, not module docstrings
-/
import Mathlib

namespace Erdos73Aristotle

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def IsIndependentSet (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ¬G.Adj u v

def IsBipartite (G : SimpleGraph V) : Prop :=
  ∃ A B : Set V, A ∪ B = Set.univ ∧ A ∩ B = ∅ ∧
    (∀ u ∈ A, ∀ v ∈ A, ¬G.Adj u v) ∧
    (∀ u ∈ B, ∀ v ∈ B, ¬G.Adj u v)

def triangleGraph : SimpleGraph (Fin 3) where
  Adj u v := u ≠ v
  symm u v h := h.symm
  loopless v := fun h => h rfl

/-
  ## Section 1: Triangle Graph Properties

  K₃ (the complete graph on 3 vertices) has specific adjacency and
  independence properties used in K3_violates_strict and K3_almost_bipartite.
-/

-- Aristotle target: adjacency in K₃ is exactly u ≠ v
theorem triangleGraph_adj_iff (u v : Fin 3) :
    triangleGraph.Adj u v ↔ u ≠ v := Iff.rfl

-- Aristotle target: any two distinct vertices in Fin 3 are adjacent in K₃
theorem triangleGraph_adj_of_ne (u v : Fin 3) (h : u ≠ v) :
    triangleGraph.Adj u v := h

-- Aristotle target: the only independent sets in K₃ are singletons and the empty set
theorem triangleGraph_indep_set_card (S : Finset (Fin 3))
    (hS : IsIndependentSet triangleGraph S) :
    S.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  exact of_not_not (hS a ha b hb)

/-
  ## Section 2: K₂ Subgraph is Bipartite

  Removing vertex 0 from K₃ leaves K₂ on {1, 2}, which is bipartite.
  This supports K3_almost_bipartite.
-/

-- Aristotle target: {1, 2} partition as A = {{1}}, B = {{2}} is a bipartition
-- The induced subgraph on {1, 2} in K₃ is bipartite
theorem triangleGraph_on_two_vertices_bipartite :
    IsBipartite (triangleGraph.induce ({(0 : Fin 3)}ᶜ : Set (Fin 3))) := by
  -- The induced subgraph on {1, 2} is K₂; bipartition A = {1}, B = {2}
  refine ⟨{⟨1, by decide⟩}, {⟨2, by decide⟩}, ?_, ?_, ?_, ?_⟩
  · -- A ∪ B = univ
    ext ⟨x, hx⟩
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
    fin_cases x <;> simp_all
  · -- A ∩ B = ∅
    ext ⟨x, hx⟩
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2⟩
    have := h1.symm.trans h2
    exact absurd (congrArg Subtype.val this) (by decide)
  · -- A is independent (singleton)
    intro u hu v hv
    simp only [Set.mem_singleton_iff] at hu hv
    rw [hu, hv]
    exact fun h => h rfl
  · -- B is independent (singleton)
    intro u hu v hv
    simp only [Set.mem_singleton_iff] at hu hv
    rw [hu, hv]
    exact fun h => h rfl

-- Aristotle target: K₃ is 1-almost-bipartite (remove vertex 0)
-- isAlmostBipartite definition: ∃ S, S.card ≤ bound ∧ IsBipartite (G.induce Sᶜ)
theorem K3_almost_bipartite_goal :
    ∃ S : Finset (Fin 3), S.card ≤ 1 ∧
      IsBipartite (triangleGraph.induce (↑Sᶜ : Set (Fin 3))) := by
  refine ⟨{0}, by simp, ?_⟩
  convert triangleGraph_on_two_vertices_bipartite using 1
  congr 1
  ext x
  simp [Finset.compl_eq_univ_sdiff]

/-
  ## Section 3: Independence Arithmetic

  Supporting the independence condition computations.
-/

-- Aristotle target: 2 * m < 2 * m + 1 (odd cycles violate k=0 condition)
theorem twice_lt_succ (m : ℕ) : 2 * m < 2 * m + 1 := by omega

-- Aristotle target: for the strict condition, 2 * I.card ≥ S.card means I.card ≥ S.card / 2
theorem strict_condition_card_bound (I S : Finset V)
    (hI : 2 * I.card ≥ S.card) :
    I.card * 2 ≥ S.card := by omega

-- Aristotle target: 3 vertices in K₃, max independent set has 1 vertex, so 2*1 < 3
theorem K3_indep_bound_fails (S : Finset (Fin 3)) (hs : S = Finset.univ)
    (I : Finset (Fin 3)) (hI : IsIndependentSet triangleGraph I)
    (hIsub : I ⊆ S) :
    ¬(2 * I.card ≥ S.card) := by
  have hcard : S.card = 3 := by rw [hs]; decide
  have hIcard := triangleGraph_indep_set_card I hI
  omega

end Erdos73Aristotle
