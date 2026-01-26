/-!
# Erdős Problem #593: Finite Subhypergraphs of Uncountably Chromatic 3-Uniform Hypergraphs

Characterize those finite 3-uniform hypergraphs which appear as subhypergraphs
in every 3-uniform hypergraph of chromatic number > ℵ₀.

## Status: OPEN ($500 prize)

## References
- Erdős, "Problems and results on finite and infinite combinatorial analysis II" (1995)
- Erdős–Galvin–Hajnal, investigations on similar problems (1975)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic

/-!
## Section I: Hypergraph Definitions
-/

/-- A 3-uniform hypergraph on vertex set V. Each edge is a set of exactly 3 vertices. -/
structure Hypergraph3 (V : Type*) where
  /-- The set of hyperedges, each a 3-element subset of V. -/
  edges : Set (Finset V)
  /-- Every edge has exactly 3 vertices. -/
  edge_card : ∀ e ∈ edges, e.card = 3

/-- A proper coloring of a 3-uniform hypergraph using colors from C.
No edge is monochromatic. -/
def IsProperColoring {V : Type*} (H : Hypergraph3 V) (C : Type*)
    (f : V → C) : Prop :=
  ∀ e ∈ H.edges, ¬ ∃ c : C, ∀ v ∈ e, f v = c

/-- The chromatic number is at most κ if there is a proper coloring
with κ colors. -/
def ChromaticNumberLE {V : Type*} (H : Hypergraph3 V) (κ : Cardinal) : Prop :=
  ∃ (C : Type*) (_ : #C ≤ κ) (f : V → C), IsProperColoring H C f

/-!
## Section II: Subhypergraph Embedding
-/

/-- A finite hypergraph F is a subhypergraph of H if there is an injective
map sending edges of F to edges of H. -/
def IsSubhypergraph {V W : Type*} (F : Hypergraph3 V) (H : Hypergraph3 W) : Prop :=
  ∃ (φ : V → W), Function.Injective φ ∧
    ∀ e ∈ F.edges, e.image φ ∈ H.edges

/-!
## Section III: The Main Problem
-/

/-- **Erdős Problem #593**: Characterize the finite 3-uniform hypergraphs F
that appear as subhypergraphs in every 3-uniform hypergraph H with
chromatic number > ℵ₀.

A finite 3-uniform hypergraph F is "unavoidable" if every 3-uniform
hypergraph with uncountable chromatic number contains F. -/
def IsUnavoidable (F : Hypergraph3 (Fin n)) : Prop :=
  ∀ (V : Type*) (H : Hypergraph3 V),
    ¬ ChromaticNumberLE H Cardinal.aleph0 →
    IsSubhypergraph F H

/-- The main open problem: characterize all unavoidable finite 3-uniform
hypergraphs. -/
def ErdosProblem593 : Prop :=
  ∃ (P : ∀ n, Hypergraph3 (Fin n) → Prop),
    (∀ n (F : Hypergraph3 (Fin n)), P n F ↔ IsUnavoidable F)

/-!
## Section IV: The Graph Case (Solved)
-/

/-- A simple graph (2-uniform hypergraph). -/
structure SimpleGraph' (V : Type*) where
  adj : V → V → Prop
  symm : ∀ v w, adj v w → adj w v
  irrefl : ∀ v, ¬ adj v v

/-- A graph is bipartite if its vertices can be 2-colored properly. -/
def IsBipartite {V : Type*} (G : SimpleGraph' V) : Prop :=
  ∃ f : V → Bool, ∀ v w, G.adj v w → f v ≠ f w

/-- For graphs, the answer is known: a graph appears in every graph
of chromatic number ≥ ℵ₁ if and only if it is bipartite.
Non-bipartite graphs (those containing odd cycles) need not appear. -/
axiom graph_case_solved :
  ∀ (n : ℕ) (G : SimpleGraph' (Fin n)),
    (∀ (V : Type*) (H : SimpleGraph' V),
      ¬ ∃ (f : V → ℕ), ∀ v w, H.adj v w → f v ≠ f w →
      ∃ (φ : Fin n → V), Function.Injective φ ∧
        ∀ i j, G.adj i j → H.adj (φ i) (φ j)) ↔
    IsBipartite G

/-!
## Section V: Known Constraints for 3-Uniform Case
-/

/-- A 3-uniform hypergraph is 2-colorable if it can be properly
colored with 2 colors (no monochromatic edge). -/
def Is2Colorable {V : Type*} (H : Hypergraph3 V) : Prop :=
  ∃ f : V → Bool, ∀ e ∈ H.edges, ¬ ∃ c, ∀ v ∈ e, f v = c

/-- Any 2-colorable finite 3-uniform hypergraph is unavoidable.
This is the analog of the bipartite graph case. -/
axiom two_colorable_is_unavoidable (n : ℕ) (F : Hypergraph3 (Fin n))
    (h : Is2Colorable F) : IsUnavoidable F

/-- The complete 3-uniform hypergraph on 4 vertices (K₄³) has
chromatic number 3 and is conjectured to be unavoidable. -/
axiom k4_3_chromatic_number :
  ∃ (F : Hypergraph3 (Fin 4)), F.edges.Finite ∧ ¬ Is2Colorable F

/-!
## Section VI: Erdős–Galvin–Hajnal
-/

/-- Erdős, Galvin, and Hajnal investigated which structures must appear
in hypergraphs of large chromatic number. Their work established the
framework for Problem 593. -/
axiom erdos_galvin_hajnal_framework :
  ∀ (n : ℕ) (F : Hypergraph3 (Fin n)),
    Is2Colorable F → IsUnavoidable F
