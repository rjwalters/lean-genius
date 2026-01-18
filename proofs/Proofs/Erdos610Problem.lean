/-
  Erdős Problem #610: Clique Transversal Numbers

  Source: https://erdosproblems.com/610
  Status: OPEN

  Statement:
  For a graph G, let τ(G) denote the clique transversal number: the minimum
  number of vertices that include at least one vertex from each maximal clique.

  Questions:
  1. Is τ(G) ≤ n - ω(n)√n for some ω(n) → ∞?
  2. Is τ(G) ≤ n - c√(n log n) for some constant c > 0?

  Known Results:
  - Erdős-Gallai-Tuza: τ(G) ≤ n - √(2n) + O(1)
  - This bound is conjectured to be nearly tight

  The problem connects to independent sets in triangle-free graphs:
  if f(n) is the max guaranteed independent set size in triangle-free graphs,
  then conjecturally τ(G) ≤ n - f(n).

  Related: Problems #151, #611
-/

import Mathlib

open Finset Function SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Cliques and Maximal Cliques -/

/-- A clique in a graph is a set of pairwise adjacent vertices -/
def IsClique (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v

/-- A clique is maximal if no proper superset is also a clique -/
def IsMaximalClique (G : SimpleGraph V) (S : Finset V) : Prop :=
  IsClique G S ∧ ∀ T : Finset V, S ⊂ T → ¬IsClique G T

/-- The set of all maximal cliques in a graph -/
noncomputable def maximalCliques (G : SimpleGraph V) : Finset (Finset V) :=
  Finset.univ.filter fun S => IsMaximalClique G S

/-! ## Clique Transversal -/

/-- A set T is a clique transversal if it intersects every maximal clique -/
def IsCliqueTransversal (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∀ C : Finset V, IsMaximalClique G C → (T ∩ C).Nonempty

/-- The clique transversal number τ(G) -/
noncomputable def cliqueTransversalNumber (G : SimpleGraph V) : ℕ :=
  Finset.univ.filter (fun T => IsCliqueTransversal G T) |>.image Finset.card |>.min' (by
    simp only [Finset.image_nonempty, Finset.filter_nonempty_iff]
    use Finset.univ
    simp [IsCliqueTransversal]
    intro C hC
    obtain ⟨v, hv⟩ := C.nonempty_of_ne_empty (by
      intro h
      simp [IsMaximalClique, IsClique] at hC
      exact hC.2 ∅ (by simp [h]) (by simp [IsClique]))
    exact ⟨v, by simp, hv⟩)

/-- Notation: τ(G) for clique transversal number -/
notation "τ" => cliqueTransversalNumber

/-! ## Basic Properties -/

/-- Every vertex set is a clique transversal -/
theorem univ_is_transversal (G : SimpleGraph V) :
    IsCliqueTransversal G Finset.univ := by
  intro C hC
  obtain ⟨v, hv⟩ := C.nonempty_of_ne_empty (by
    intro h
    simp [IsMaximalClique, IsClique] at hC
    exact hC.2 ∅ (by simp [h]) (by simp [IsClique]))
  exact ⟨v, by simp, hv⟩

/-- τ(G) ≤ n -/
theorem tau_le_card (G : SimpleGraph V) : τ G ≤ Fintype.card V := by
  sorry

/-- Empty graph: every vertex is a maximal clique (singleton) -/
theorem tau_empty : τ (⊥ : SimpleGraph V) = Fintype.card V := by
  sorry

/-- Complete graph: τ = 1 (single maximal clique = all vertices) -/
theorem tau_complete [Nontrivial V] : τ (⊤ : SimpleGraph V) = 1 := by
  sorry

/-! ## The Erdős-Gallai-Tuza Bound -/

/-- The known upper bound: τ(G) ≤ n - √(2n) + O(1) -/
def ErdosGallaiTuzaBound (n : ℕ) : ℝ :=
  n - Real.sqrt (2 * n)

theorem erdos_gallai_tuza :
    ∃ C : ℝ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (τ G : ℝ) ≤ Fintype.card V - Real.sqrt (2 * Fintype.card V) + C := by
  sorry

/-! ## The Main Questions (OPEN) -/

/-- Question 1: Can we improve to n - ω(n)√n for ω(n) → ∞? -/
def Question1_OmegaImprovement : Prop :=
  ∃ ω : ℕ → ℝ, (∀ n, ω n > 0) ∧ Filter.Tendsto ω Filter.atTop Filter.atTop ∧
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (τ G : ℝ) ≤ Fintype.card V - ω (Fintype.card V) * Real.sqrt (Fintype.card V)

/-- Question 2: Can we achieve n - c√(n log n) for constant c > 0? -/
def Question2_LogImprovement : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      let n := Fintype.card V
      (τ G : ℝ) ≤ n - c * Real.sqrt (n * Real.log n)

/-! ## Connection to Independent Sets -/

/-- An independent set has no edges between its vertices -/
def IsIndependentSet (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ¬G.Adj u v

/-- The independence number α(G) -/
noncomputable def independenceNumber (G : SimpleGraph V) : ℕ :=
  Finset.univ.filter (fun S => IsIndependentSet G S) |>.image Finset.card |>.max' (by
    simp [Finset.image_nonempty, Finset.filter_nonempty_iff]
    use ∅
    simp [IsIndependentSet])

/-- A graph is triangle-free if it has no 3-cliques -/
def IsTriangleFree (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, S.card = 3 → ¬IsClique G S

/-- f(n) = min guaranteed independence number in triangle-free graphs on n vertices -/
noncomputable def triangleFreeIndependence (n : ℕ) : ℕ :=
  sorry -- The minimum over all triangle-free graphs on n vertices

/-! ## The Erdős-Gallai-Tuza Conjecture -/

/-- Conjecture: τ(G) ≤ n - f(n) where f is the triangle-free independence function -/
def ErdosGallaiTuzaConjecture : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    τ G ≤ Fintype.card V - triangleFreeIndependence (Fintype.card V)

/-- Kim's result: f(n) = Θ(√(n log n)) for triangle-free graphs -/
axiom kim_triangle_free_independence :
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ n ≥ 2,
    c₁ * Real.sqrt (n * Real.log n) ≤ triangleFreeIndependence n ∧
    (triangleFreeIndependence n : ℝ) ≤ c₂ * Real.sqrt (n * Real.log n)

/-- If the conjecture holds, Question 2 follows -/
theorem conjecture_implies_question2 :
    ErdosGallaiTuzaConjecture → Question2_LogImprovement := by
  sorry

/-! ## Lower Bounds -/

/-- There exist graphs where τ(G) is close to n - √(2n) -/
def NearTightConstruction : Prop :=
  ∀ ε > 0, ∃ᶠ n in Filter.atTop, ∃ (V : Type*) [Fintype V] [DecidableEq V],
    ∃ G : SimpleGraph V,
      Fintype.card V = n ∧
      (τ G : ℝ) ≥ n - (1 + ε) * Real.sqrt (2 * n)

/-- The Erdős-Gallai-Tuza bound is essentially tight -/
theorem egt_bound_tight : NearTightConstruction := by
  sorry

/-! ## Special Cases -/

/-- For bipartite graphs, τ relates to vertex covers -/
theorem tau_bipartite (G : SimpleGraph V) (hG : G.IsBipartite) :
    τ G = sorry -- Related to minimum vertex cover
    := by sorry

/-- For chordal graphs, τ can be computed efficiently -/
theorem tau_chordal (G : SimpleGraph V) (hG : sorry) : -- G is chordal
    sorry -- τ(G) has nice structure
    := by sorry

/-- For perfect graphs -/
theorem tau_perfect (G : SimpleGraph V) (hG : sorry) : -- G is perfect
    sorry -- τ(G) relates to chromatic number
    := by sorry

/-! ## Clique Cover Duality -/

/-- A clique cover partitions vertices into cliques -/
def IsCliqueCover (G : SimpleGraph V) (C : Finset (Finset V)) : Prop :=
  (∀ S ∈ C, IsClique G S) ∧ (C : Set (Finset V)).PairwiseDisjoint id ∧
  Finset.univ = C.biUnion id

/-- The clique cover number -/
noncomputable def cliqueCoverNumber (G : SimpleGraph V) : ℕ :=
  sorry -- Minimum number of cliques needed to cover all vertices

/-- Relationship between τ and clique cover -/
theorem tau_clique_cover_relation (G : SimpleGraph V) :
    τ G ≥ cliqueCoverNumber G := by
  sorry

/-! ## Main Problem Statement -/

/-- Erdős Problem #610: OPEN

    Known: τ(G) ≤ n - √(2n) + O(1) (Erdős-Gallai-Tuza)
    Open: Can this be improved to n - ω(n)√n or n - c√(n log n)?

    The conjecture τ(G) ≤ n - f(n) would resolve Question 2. -/
theorem erdos_610_known :
    ∃ C : ℝ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (τ G : ℝ) ≤ Fintype.card V - Real.sqrt (2 * Fintype.card V) + C :=
  erdos_gallai_tuza

/-- The problem remains open -/
theorem erdos_610_open : Question1_OmegaImprovement ↔ Question1_OmegaImprovement := Iff.rfl

#check erdos_610_known
#check Question1_OmegaImprovement
#check Question2_LogImprovement
#check ErdosGallaiTuzaConjecture
