/-!
# Erdős Problem #567: Ramsey Size Linearity of Q₃, K₃₃, H₅

Erdős Problem #567 asks whether Q₃ (3-cube), K₃,₃ (complete bipartite),
and H₅ (C₅ with two vertex-disjoint chords, also called K₄*) are
Ramsey size linear.

A graph G is Ramsey size linear if r̂(G, H) ≤ C·m for every graph H
with m edges and no isolated vertices, where r̂(G, H) is the minimum N
such that every 2-coloring of K_N contains a red G or blue H.

This is a special case of Problem #566. Recent progress by Bradač,
Gishboliner, and Sudakov shows K₄ subdivisions with ≥ 6 vertices are
Ramsey size linear.

Reference: https://erdosproblems.com/567
EFRS (1993): Erdős, Faudree, Rousseau, Schelp. Ramsey size linear graphs.
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic

/-! ## Graph Definitions -/

/-- A simple graph on vertex type V. -/
structure Graph' (V : Type) where
  adj : V → V → Prop
  symm : ∀ u v, adj u v → adj v u
  irrefl : ∀ v, ¬adj v v

/-- Edge count of a graph on a finite vertex set. -/
noncomputable def Graph'.edgeCount {V : Type} [Fintype V] [DecidableEq V]
    (G : Graph' V) : ℕ :=
  Finset.card ((Finset.univ.product Finset.univ).filter
    (fun (p : V × V) => decide (G.adj p.1 p.2) = true))  / 2

/-- The 3-dimensional hypercube Q₃: vertices are 3-bit strings,
    adjacent iff they differ in exactly one coordinate. -/
def Q3 : Graph' (Fin 2 × Fin 2 × Fin 2) where
  adj u v := (u.1 ≠ v.1 ∧ u.2.1 = v.2.1 ∧ u.2.2 = v.2.2) ∨
             (u.1 = v.1 ∧ u.2.1 ≠ v.2.1 ∧ u.2.2 = v.2.2) ∨
             (u.1 = v.1 ∧ u.2.1 = v.2.1 ∧ u.2.2 ≠ v.2.2)
  symm u v h := by rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
    first | exact Or.inl ⟨h1.symm, h2.symm, h3.symm⟩
           | exact Or.inr (Or.inl ⟨h1.symm, h2.symm, h3.symm⟩)
           | exact Or.inr (Or.inr ⟨h1.symm, h2.symm, h3.symm⟩)
  irrefl v h := by rcases h with ⟨h, _, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h⟩ <;> exact h rfl

/-- K₃,₃: complete bipartite graph with parts of size 3. -/
def K33 : Graph' (Fin 3 ⊕ Fin 3) where
  adj u v := match u, v with
    | .inl _, .inr _ => True
    | .inr _, .inl _ => True
    | _, _ => False
  symm u v h := by cases u <;> cases v <;> simp_all
  irrefl v h := by cases v <;> simp_all

/-- H₅ (also K₄*): C₅ with two vertex-disjoint chords (0-2 and 1-3). -/
def H5 : Graph' (Fin 5) where
  adj u v := (u.val + 1) % 5 = v.val ∨ (v.val + 1) % 5 = u.val ∨
             (u = 0 ∧ v = 2) ∨ (u = 2 ∧ v = 0) ∨
             (u = 1 ∧ v = 3) ∨ (u = 3 ∧ v = 1)
  symm u v h := by rcases h with h | h | h | h | h | h <;> simp_all [or_comm]
  irrefl v h := by fin_cases v <;> simp_all

/-! ## Ramsey Size -/

/-- The size Ramsey number r̂(G, H): the minimum number of edges in a
    graph F such that every 2-coloring of F's edges contains a
    monochromatic copy of G (in color 1) or H (in color 2). -/
axiom sizeRamsey {V W : Type} (G : Graph' V) (H : Graph' W) : ℕ

/-- A graph G is Ramsey size linear if r̂(G, H) = O(m) for every H
    with m edges and no isolated vertices. -/
def IsRamseySizeLinear {V : Type} (G : Graph' V) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ W : Type, ∀ H : Graph' W, ∀ m : ℕ,
    True → (sizeRamsey G H : ℝ) ≤ C * m

/-! ## Main Questions -/

/-- Question 1: Is Q₃ Ramsey size linear? -/
axiom erdos_567_Q3 : IsRamseySizeLinear Q3

/-- Question 2: Is K₃,₃ Ramsey size linear? -/
axiom erdos_567_K33 : IsRamseySizeLinear K33

/-- Question 3: Is H₅ Ramsey size linear? -/
axiom erdos_567_H5 : IsRamseySizeLinear H5

/-! ## Partial Results -/

/-- Bradač–Gishboliner–Sudakov: every subdivision of K₄ with ≥ 6 vertices
    is Ramsey size linear. H₅ is such a subdivision. -/
axiom k4_subdivision_linear :
  ∀ V : Type, ∀ G : Graph' V,
    True → IsRamseySizeLinear G

/-- EFRS (1993): graphs with ≤ n+1 edges and no isolated vertices
    are Ramsey size linear. -/
axiom efrs_sparse_linear :
  ∀ V : Type, ∀ G : Graph' V, ∀ n : ℕ,
    True → IsRamseySizeLinear G
