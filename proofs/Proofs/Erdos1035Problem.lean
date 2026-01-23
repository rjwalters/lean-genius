/-
Erdős Problem #1035: Hypercube Subgraphs via Minimum Degree

**Statement**: Is there a constant c > 0 such that every graph on 2^n vertices
with minimum degree > (1-c)·2^n contains the n-dimensional hypercube Q_n?

**Status**: OPEN

**Related Questions** (if main conjecture is false):
1. Find smallest m > 2^n such that min degree > (1-c)·2^n guarantees Q_n
2. Find u_n such that min degree > 2^n - u_n guarantees Q_n

Reference: https://erdosproblems.com/1035
See also problem #576 for extremal edge count.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card

open Nat

namespace Erdos1035

variable {V : Type*} [Fintype V] [DecidableEq V]

/-
## Part I: The Hypercube Graph Q_n
-/

/-- The n-dimensional hypercube Q_n has vertices {0,1}^n.
    Two vertices are adjacent iff they differ in exactly one coordinate. -/
def hypercube (n : ℕ) : SimpleGraph (Fin n → Bool) where
  Adj x y := (Finset.univ.filter fun i => x i ≠ y i).card = 1
  symm := by
    intro x y h
    simp only [Finset.filter_congr_decidable] at h ⊢
    convert h using 2
    ext i
    exact ne_comm
  loopless := by
    intro x h
    simp only [Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies, ne_eq,
               not_true_eq_false] at h
    have : (Finset.univ.filter fun i => x i ≠ x i).card = 0 := by
      simp [Finset.filter_eq_empty_iff]
    omega

/-- Q_n has 2^n vertices. -/
theorem hypercube_card (n : ℕ) : Fintype.card (Fin n → Bool) = 2^n := by
  simp [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

/-- Q_n is n-regular: every vertex has degree n. -/
theorem hypercube_regular (n : ℕ) (v : Fin n → Bool) :
    (hypercube n).degree v = n := by
  -- degree = |neighborFinset| = |{w : w differs from v in exactly 1 coord}|
  -- There's a bijection between neighbors and Fin n: the coordinate that differs
  rw [SimpleGraph.degree]
  -- The neighbor finset consists of vertices differing in exactly one coordinate
  -- We show there's a bijection with Fin n
  have h : (hypercube n).neighborFinset v = Finset.univ.image (fun i => Function.update v i (!v i)) := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, hypercube, Function.update, Finset.mem_image,
               Finset.mem_univ, true_and]
    constructor
    · -- If w is a neighbor, it differs in exactly one coordinate i
      intro hadj
      -- hadj says exactly one coord differs
      have hone : (Finset.univ.filter fun i => v i ≠ w i).card = 1 := hadj
      obtain ⟨i, hi, huniq⟩ := Finset.card_eq_one.mp hone
      use i
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      by_cases hji : j = i
      · subst hji
        simp [hi]
      · have : v j = w j := by
          by_contra h
          have hj : j ∈ Finset.univ.filter (fun i => v i ≠ w i) := by simp [h]
          have : j = i := huniq j hj
          contradiction
        simp [hji, this]
    · -- If w = update v i (¬v i) for some i, then w differs in exactly one coord
      rintro ⟨i, rfl⟩
      have : (Finset.univ.filter fun j => v j ≠ (if j = i then !v i else v j)).card = 1 := by
        have hsing : Finset.univ.filter (fun j => v j ≠ (if j = i then !v i else v j)) = {i} := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro h
            by_contra hne
            simp [hne] at h
          · intro hji
            subst hji
            simp [Bool.not_eq_self]
        rw [hsing, Finset.card_singleton]
      convert this using 2
      ext j
      simp [Function.update_apply]
  rw [h]
  -- Now show |image of Fin n| = n
  have hinj : Function.Injective (fun i => Function.update v i (!v i)) := by
    intro i j hij
    by_contra hne
    have : Function.update v i (!v i) i = Function.update v j (!v j) i := by rw [hij]
    simp [Function.update_same, Function.update_noteq hne] at this
    exact Bool.not_eq_self (v i) this
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-
## Part II: Graph Containment
-/

/-- G contains H as a subgraph if there's an embedding. -/
def ContainsSubgraph (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : W → V, Function.Injective f ∧ ∀ x y, H.Adj x y → G.Adj (f x) (f y)

/-- G contains Q_n. -/
def ContainsHypercube (G : SimpleGraph V) (n : ℕ) : Prop :=
  ContainsSubgraph G (hypercube n)

/-
## Part III: Minimum Degree
-/

/-- Minimum degree of a graph. -/
noncomputable def minDegree (G : SimpleGraph V) : ℕ :=
  Finset.univ.inf' ⟨Classical.arbitrary V, Finset.mem_univ _⟩ G.degree

/-- G has minimum degree at least k. -/
def HasMinDegree (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ v : V, G.degree v ≥ k

/-
## Part IV: The Main Conjecture
-/

/-- The main conjecture: there exists c > 0 such that for all n,
    any graph on 2^n vertices with min degree > (1-c)·2^n contains Q_n. -/
def mainConjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 →
    ∀ G : SimpleGraph (Fin (2^n)),
      (∀ v, (G.degree v : ℝ) > (1 - c) * 2^n) →
      ContainsHypercube G n

/-- Alternative formulation with explicit threshold. -/
def mainConjectureExplicit (c : ℝ) (hc : c > 0) : Prop :=
  ∀ n : ℕ, n ≥ 1 →
    ∀ G : SimpleGraph (Fin (2^n)),
      HasMinDegree G (⌊(1 - c) * 2^n⌋₊ + 1) →
      ContainsHypercube G n

/-
## Part V: Related Questions (if conjecture is false)
-/

/-- Question 1: What's the smallest m > 2^n that works?
    Find smallest m such that any graph on m vertices with
    min degree > (1-c)·2^n contains Q_n. -/
def question1 (c : ℝ) (n : ℕ) : ℕ :=
  Nat.find ⟨2^n * 2^n, by sorry⟩  -- Some upper bound exists

/-- Question 2: What's the right u_n?
    Find u_n such that min degree > 2^n - u_n guarantees Q_n. -/
def question2 (n : ℕ) : ℕ :=
  Nat.find ⟨2^n, by sorry⟩  -- Trivial upper bound

/-
## Part VI: Basic Properties
-/

/-- A complete graph on 2^n vertices contains Q_n. -/
theorem complete_contains_hypercube (n : ℕ) :
    ContainsHypercube (⊤ : SimpleGraph (Fin (2^n))) n := by
  -- The complete graph contains any graph on the same number of vertices
  -- We need to embed (Fin n → Bool) into Fin (2^n)
  unfold ContainsHypercube ContainsSubgraph
  -- Use the equivalence (Fin n → Bool) ≃ Fin (2^n)
  have hcard : Fintype.card (Fin n → Bool) = 2^n := hypercube_card n
  -- Get an equivalence using Fintype.equivOfCardEq
  have equiv : (Fin n → Bool) ≃ Fin (2^n) := by
    exact Fintype.equivOfCardEq (by rw [hcard, Fintype.card_fin])
  use equiv
  constructor
  · exact equiv.injective
  · intro x y hxy
    -- In the complete graph, all distinct vertices are adjacent
    simp only [SimpleGraph.top_adj]
    intro heq
    -- If equiv x = equiv y, then x = y
    have : x = y := equiv.injective heq
    -- But x and y are adjacent in the hypercube, so x ≠ y
    unfold hypercube at hxy
    simp only at hxy
    have hne : (Finset.univ.filter fun i => x i ≠ y i).card = 1 := hxy
    have : x ≠ y := by
      intro hxy'
      subst hxy'
      simp at hne
    contradiction

/-- Q_n has 2^(n-1)·n edges. -/
theorem hypercube_edge_count (n : ℕ) (hn : n ≥ 1) :
    (hypercube n).edgeFinset.card = 2^(n-1) * n := by
  sorry

/-- Lower bound: if min degree is too low, Q_n might not exist. -/
axiom lower_bound_necessary :
    ∀ n ≥ 1, ∃ G : SimpleGraph (Fin (2^n)),
      HasMinDegree G (2^(n-1)) ∧ ¬ContainsHypercube G n

/-
## Part VII: Summary
-/

/-- Erdős Problem #1035: Summary

    **Conjecture**: ∃ c > 0 such that any graph on 2^n vertices with
    min degree > (1-c)·2^n contains the n-cube Q_n.

    **Key Structure**:
    - Q_n has 2^n vertices, n-regular
    - Q_n has 2^{n-1}·n edges
    - Vertices are {0,1}^n, adjacent iff differ in one bit

    **If false, study**:
    1. Minimum m > 2^n that works
    2. Threshold u_n for min degree 2^n - u_n

    **Related**: Problem #576 for edge extremal problem. -/
theorem erdos_1035_summary :
    -- Q_n basic properties
    (∀ n, Fintype.card (Fin n → Bool) = 2^n) ∧
    -- Complete graph works
    (∀ n, ContainsHypercube (⊤ : SimpleGraph (Fin (2^n))) n) := by
  constructor
  · intro n; exact hypercube_card n
  · intro n; exact complete_contains_hypercube n

end Erdos1035
