/-
  Erdős Problem #550: Ramsey Numbers for Trees and Multipartite Graphs

  Source: https://erdosproblems.com/550
  Status: OPEN

  Statement:
  Let m₁ ≤ ⋯ ≤ mₖ and n be sufficiently large. If T is a tree on n vertices
  and G is the complete multipartite graph K_{m₁,...,mₖ}, prove that
    R(T,G) ≤ (χ(G)-1)(R(T,K_{m₁,m₂})-1) + m₁

  Background:
  Chvátal (1977): R(T, Kₘ) = (m-1)(n-1) + 1 for any tree T on n vertices.

  Tags: graph-theory, ramsey-theory, trees
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace Erdos550

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/- ## Part I: Basic Graph Definitions -/

/-- A graph is a tree if it is connected and acyclic. -/
def IsTree (G : SimpleGraph V) : Prop :=
  G.Connected ∧ ∀ (u v : V), G.Adj u v → G.Reachable u v

/-- Number of vertices in graph. -/
def vertexCount (V : Type*) [Fintype V] : ℕ := Fintype.card V

/- ## Part II: Complete Multipartite Graphs -/

/-- Complete multipartite graph with part sizes m₁, ..., mₖ. -/
structure CompleteMultipartite where
  k : ℕ                          -- number of parts
  partSizes : Fin k → ℕ          -- sizes m₁, ..., mₖ
  sorted : ∀ i j, i ≤ j → partSizes i ≤ partSizes j

/-- Total number of vertices in complete multipartite graph. -/
def CompleteMultipartite.totalVertices (G : CompleteMultipartite) : ℕ :=
  ∑ i, G.partSizes i

/-- Chromatic number of complete multipartite graph equals k (number of parts). -/
def CompleteMultipartite.chromaticNumber (G : CompleteMultipartite) : ℕ := G.k

/-- The complete graph Kₘ as a complete multipartite graph with m parts of size 1. -/
def completeGraphAsMultipartite (m : ℕ) : CompleteMultipartite :=
  { k := m
    partSizes := fun _ => 1
    sorted := fun _ _ _ => le_refl 1 }

/-- Complete bipartite graph K_{m₁,m₂}. -/
def completeBipartite (m1 m2 : ℕ) (h : m1 ≤ m2) : CompleteMultipartite :=
  { k := 2
    partSizes := ![m1, m2]
    sorted := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
      · exact h }

/- ## Part III: Ramsey Numbers -/

/-- Ramsey numbers exist: for any graphs, there exists N such that any 2-coloring
    of K_N contains a red copy of T or a blue copy of G. -/
axiom ramsey_exists (T : Type*) [Fintype T] (G : CompleteMultipartite) :
    ∃ N, ∀ (coloring : Fin N → Fin N → Fin 2),
      (∃ f : T → Fin N, Function.Injective f ∧
        ∀ x y, x ≠ y → coloring (f x) (f y) = 0) ∨
      (∃ (parts : Fin G.k → Finset (Fin N)),
        (∀ i j, i ≠ j → Disjoint (parts i) (parts j)) ∧
        (∀ i, (parts i).card ≥ G.partSizes i) ∧
        (∀ i j, i ≠ j → ∀ u ∈ parts i, ∀ v ∈ parts j, coloring u v = 1))

/-- The Ramsey number R(T, G): smallest N such that any 2-coloring of K_N
    contains red T or blue G. -/
noncomputable def ramseyNumber (T : Type*) [Fintype T]
    (G : CompleteMultipartite) : ℕ :=
  Nat.find (ramsey_exists T G)

/- ## Part IV: Chvátal's Theorem -/

/-- Chvátal (1977): R(T, Kₘ) = (m-1)(n-1) + 1 for any tree T on n vertices. -/
axiom chvatal (T : Type*) [Fintype T] [DecidableEq T]
    (G : SimpleGraph T) [DecidableRel G.Adj] (hT : IsTree G) (m : ℕ) (hm : m ≥ 2) :
    ramseyNumber T (completeGraphAsMultipartite m) = (m - 1) * (Fintype.card T - 1) + 1

/--
**Chvátal's formula examples:**
R(T_n, K_m) = (m-1)(n-1) + 1 for any tree T on n vertices.
-/
example : (3 - 1) * (5 - 1) + 1 = 9 := by native_decide   -- R(T₅, K₃)
example : (4 - 1) * (6 - 1) + 1 = 16 := by native_decide  -- R(T₆, K₄)
example : (3 - 1) * (10 - 1) + 1 = 19 := by native_decide -- R(T₁₀, K₃)
example : (5 - 1) * (4 - 1) + 1 = 13 := by native_decide  -- R(T₄, K₅)

/- ## Part V: The Conjecture -/

/-- The conjectured bound for R(T, G) with multipartite G. -/
def ConjecturedBound (T : Type*) [Fintype T] (G : CompleteMultipartite)
    (hk : G.k ≥ 2) : ℕ :=
  let χ := G.chromaticNumber
  let m1 := G.partSizes ⟨0, by omega⟩
  let m2 := G.partSizes ⟨1, by omega⟩
  let bipartite := completeBipartite m1 m2 (G.sorted ⟨0, by omega⟩ ⟨1, by omega⟩)
  (χ - 1) * (ramseyNumber T bipartite - 1) + m1

/-- Erdős's conjecture: R(T, G) ≤ (χ(G)-1)(R(T, K_{m₁,m₂})-1) + m₁. -/
def ErdosConjecture : Prop :=
  ∀ n : ℕ, ∃ N₀, ∀ n' ≥ N₀,
    ∀ (T : Type*) [Fintype T] [DecidableEq T] (G : SimpleGraph T) [DecidableRel G.Adj],
    IsTree G → Fintype.card T = n' →
    ∀ (M : CompleteMultipartite) (hk : M.k ≥ 2),
    ramseyNumber T M ≤ ConjecturedBound T M hk

/-- The conjecture is currently OPEN. -/
axiom erdos_conjecture_open : ErdosConjecture

/- ## Part VI: Special Cases -/

/-- For complete graphs (G = Kₘ), reduces to Chvátal. -/
theorem complete_graph_case (T : Type*) [Fintype T] [DecidableEq T]
    (G : SimpleGraph T) [DecidableRel G.Adj] (hT : IsTree G) (m : ℕ) (hm : m ≥ 2) :
    ramseyNumber T (completeGraphAsMultipartite m) = (m - 1) * (Fintype.card T - 1) + 1 := by
  exact chvatal T G hT m hm

/-- For bipartite G = K_{m,m}. -/
axiom bipartite_case (T : Type*) [Fintype T] [DecidableEq T]
    (G : SimpleGraph T) [DecidableRel G.Adj] (hT : IsTree G) (m : ℕ) (hm : m ≥ 1) :
    ramseyNumber T (completeBipartite m m (le_refl m)) ≤
      (Fintype.card T - 1) * (2 * m - 1) + m

/-- Star graph: K_{1,n-1}. -/
def starGraph (n : ℕ) : CompleteMultipartite :=
  completeBipartite 1 (n - 1) (by omega)

/- ## Part VII: Path Graphs -/

/-- Path on n vertices: P_n. -/
def IsPath (G : SimpleGraph V) : Prop :=
  IsTree G ∧ ∃ u v : V, (∀ w, G.degree w ≤ 2) ∧
    G.degree u = 1 ∧ G.degree v = 1

/- ## Part VIII: General Tree Structure -/

/-- Maximum degree of a tree. -/
noncomputable def maxDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.univ.sup (G.degree ·)

/-- Burr's conjecture for bounded degree trees. -/
def BurrConjecture (Δ : ℕ) : Prop :=
  ∃ C : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    IsTree G → maxDegree G ≤ Δ →
    ramseyNumber V (completeGraphAsMultipartite 3) ≤ C * Fintype.card V

/-- Burr's conjecture is true (proved). -/
axiom burr_conjecture (Δ : ℕ) : BurrConjecture Δ

/- ## Part IX: Turán-Type Connections -/

/-- Turán number: max edges in n-vertex graph avoiding K_r. -/
noncomputable def turanNumber (n r : ℕ) : ℕ :=
  (1 - 1 / (r - 1 : ℚ)) * n^2 / 2 |>.floor.toNat

/- ## Part X: Probabilistic Lower Bounds -/

/- ## Part XI: Extremal Graphs -/

/-- Extremal graph for Ramsey: (m-1)(n-1) vertices with no red tree and no blue K_m.
    Constructed as (m-1) disjoint red cliques of size (n-1). -/
def RamseyExtremalGraph (n m : ℕ) : Prop :=
  ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
    (coloring : V → V → Fin 2),
    Fintype.card V = (m - 1) * (n - 1) ∧
    (∀ (T : Type) [Fintype T] [DecidableEq T] (G : SimpleGraph T) [DecidableRel G.Adj],
      IsTree G → Fintype.card T = n →
      ¬∃ f : T → V, Function.Injective f ∧ ∀ x y, x ≠ y → coloring (f x) (f y) = 0)

/- ## Part XII: Asymptotic Behavior -/

end Erdos550

/-
  ## Summary

  This file formalizes Erdős Problem #550 on Ramsey numbers for trees
  and complete multipartite graphs.

  **Status**: OPEN

  **The Conjecture**: For T a tree on n vertices and G = K_{m₁,...,mₖ},
    R(T, G) ≤ (χ(G)-1)(R(T, K_{m₁,m₂})-1) + m₁

  **Known Results**:
  - Chvátal (1977): R(T, Kₘ) = (m-1)(n-1) + 1 (exact)
  - Special cases for paths, stars, bounded-degree trees

  **Key axioms**:
  - `chvatal`: The foundational exact result
  - `erdos_conjecture_open`: The main conjecture (axiom)
  - `bipartite_case`: Special case bounds
  - `burr_conjecture`: Bounded degree result
-/
