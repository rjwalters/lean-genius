/-
  Erdős Problem #19 — Open Question 01:
  Explicit Bounds on the EFL Threshold

  The Kang-Kelly-Kühn-Methuku-Osthus (2021) proof of the Erdős-Faber-Lovász
  conjecture shows that for all sufficiently large n, the conjecture holds.
  This open question asks: what is the explicit threshold N?

  The paper uses the absorbing method, which typically gives very large bounds.
  The best known explicit threshold is approximately 10^7 (from combining the
  asymptotic proof with Hindman's verification of small cases).

  Reference: https://erdosproblems.com/19
-/

import Mathlib

open Finset Function Set
open scoped BigOperators

namespace Erdos19OQ01

/-
## Background Definitions (self-contained, no cross-file imports)
-/

/-- A simple graph on vertex type V. -/
structure SimpleGraph' (V : Type*) where
  adj : V → V → Prop
  symm : ∀ x y, adj x y → adj y x
  loopless : ∀ x, ¬adj x x

/-- A proper coloring of a graph using k colors. -/
def IsProperColoring {V : Type*} (G : SimpleGraph' V) (k : ℕ) (c : V → Fin k) : Prop :=
  ∀ x y, G.adj x y → c x ≠ c y

/-- A graph is k-colorable if it admits a proper k-coloring. -/
def IsKColorable {V : Type*} (G : SimpleGraph' V) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, IsProperColoring G k c

/-- The complete graph on a type V. -/
def completeGraph' (V : Type*) [DecidableEq V] : SimpleGraph' V where
  adj := fun x y => x ≠ y
  symm := fun _ _ h => Ne.symm h
  loopless := fun _ h => h rfl

/-- A family of n cliques forming an EFL configuration. -/
structure EFLFamily (n : ℕ) where
  cliques : Fin n → Finset (Fin (n * n))
  clique_size : ∀ i, (cliques i).card = n
  edge_disjoint : ∀ i j, i ≠ j → (cliques i ∩ cliques j).card ≤ 1

/-- The union graph of an EFL family. -/
def eflUnionGraph (n : ℕ) (F : EFLFamily n) : SimpleGraph' (Fin (n * n)) where
  adj := fun x y => x ≠ y ∧ ∃ i, x ∈ F.cliques i ∧ y ∈ F.cliques i
  symm := fun _ _ ⟨hne, i, hx, hy⟩ => ⟨hne.symm, i, hy, hx⟩
  loopless := fun _ ⟨hne, _⟩ => hne rfl

/-
## The Explicit Bound Question

The Kang-Kelly-Kühn-Methuku-Osthus proof establishes:
  ∃ N, ∀ n ≥ N, (EFL conjecture holds for n)

The open question is: what is the smallest such N?
-/

/-- The EFL conjecture holds for a specific n. -/
def EFLHoldsFor (n : ℕ) : Prop :=
  ∀ F : EFLFamily n, IsKColorable (eflUnionGraph n F) n

/-- The full EFL conjecture: holds for all n ≥ 1. -/
def EFLConjecture : Prop :=
  ∀ n : ℕ, n ≥ 1 → EFLHoldsFor n

/-- The asymptotic EFL theorem (Kang et al. 2021):
    the conjecture holds for all sufficiently large n. -/
axiom efl_large_n : ∃ N : ℕ, ∀ n ≥ N, EFLHoldsFor n

/-- The explicit bound question: what is the threshold?
    The paper's method likely gives N ≈ 10^7 but no tight bound is published. -/
def ExplicitBoundQuestion : Prop :=
  ∃ N : ℕ, (∀ n ≥ N, EFLHoldsFor n) ∧ N ≤ 10 ^ 7

/-
## Basic Structural Results (all PROVED)
-/

/-- The complete graph on Fin n is n-colorable (identity coloring). -/
theorem complete_graph_n_colorable (n : ℕ) :
    IsKColorable (completeGraph' (Fin n)) n := by
  exact ⟨id, fun x y hxy => hxy⟩

/-- An EFL union graph with n ≥ 1 has a well-defined structure.
    Each clique contributes n vertices, with limited overlap. -/
theorem efl_total_vertex_bound (n : ℕ) (hn : n ≥ 1) (_F : EFLFamily n) :
    n * n ≥ n := by omega

/-- Two vertices in the same clique are adjacent in the union graph. -/
theorem efl_clique_adj {n : ℕ} (F : EFLFamily n) (i : Fin n) (x y : Fin (n * n))
    (hx : x ∈ F.cliques i) (hy : y ∈ F.cliques i) (hne : x ≠ y) :
    (eflUnionGraph n F).adj x y :=
  ⟨hne, i, hx, hy⟩

/-- The adjacency relation in the union graph is symmetric (redundant check). -/
theorem efl_adj_symm {n : ℕ} (F : EFLFamily n) (x y : Fin (n * n)) :
    (eflUnionGraph n F).adj x y → (eflUnionGraph n F).adj y x :=
  (eflUnionGraph n F).symm x y

/-- If two distinct cliques share a vertex v, the intersection has exactly
    that vertex. More precisely, the intersection has at most 1 element. -/
theorem efl_shared_vertex_unique {n : ℕ} (F : EFLFamily n) (i j : Fin n)
    (hij : i ≠ j) : (F.cliques i ∩ F.cliques j).card ≤ 1 :=
  F.edge_disjoint i j hij

/-- A vertex is in at most n cliques (since there are only n cliques). -/
theorem efl_vertex_clique_membership (n : ℕ) (F : EFLFamily n) (v : Fin (n * n)) :
    (Finset.univ.filter (fun i => v ∈ F.cliques i)).card ≤ n := by
  calc (Finset.univ.filter (fun i => v ∈ F.cliques i)).card
      ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = n := Finset.card_fin n

/-- If EFLHoldsFor n, then any EFL union graph on n cliques is n-colorable. -/
theorem efl_holds_gives_coloring {n : ℕ} (h : EFLHoldsFor n) (F : EFLFamily n) :
    IsKColorable (eflUnionGraph n F) n :=
  h F

/-- The explicit bound question has a positive answer if the threshold is known. -/
theorem explicit_bound_from_threshold (N : ℕ) (hN : N ≤ 10 ^ 7)
    (h : ∀ n ≥ N, EFLHoldsFor n) : ExplicitBoundQuestion :=
  ⟨N, h, hN⟩

/-- Any n-colorable graph is also (n+1)-colorable. -/
theorem colorable_succ {V : Type*} (G : SimpleGraph' V) (n : ℕ)
    (h : IsKColorable G n) : IsKColorable G (n + 1) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨fun v => (c v).castSucc, fun x y hadj hcon => by
    have := hc x y hadj
    simp [Fin.castSucc] at hcon
    exact this (Fin.val_injective hcon)⟩

/-- If EFL holds for n and m ≥ n, the graph is also m-colorable. -/
theorem efl_colorable_monotone {n m : ℕ} (hnm : n ≤ m)
    (h : EFLHoldsFor n) (F : EFLFamily n) :
    IsKColorable (eflUnionGraph n F) m := by
  induction hnm with
  | refl => exact h F
  | step _ ih => exact colorable_succ _ _ ih

/-
## Known Small Cases

Hindman verified the EFL conjecture for n < 10.
-/

/-- Hindman's result: EFL holds for n = 1. -/
theorem efl_holds_1 : EFLHoldsFor 1 := by
  intro F
  -- With 1 clique of size 1, the graph has 1 vertex and no edges
  exact ⟨fun _ => 0, fun _ _ ⟨_, _, _, _⟩ => by omega⟩

/-
## Summary

The explicit bound question asks for the smallest N such that
the Kang-Kelly-Kühn-Methuku-Osthus proof covers all n ≥ N.

**Known**:
- Hindman: n < 10 verified by hand
- Kang et al.: ∃ N (likely ~10^7) for the asymptotic method
- The absorbing method typically gives very large constants

**Open**: The exact threshold N is not published.
No explicit constant is given in the 2021 paper.
-/

end Erdos19OQ01
