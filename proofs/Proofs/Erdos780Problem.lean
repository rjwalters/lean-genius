/-!
Erdős Problem #780: Chromatic Number of Kneser Hypergraphs

Source: https://erdosproblems.com/780
Status: SOLVED (Alon-Frankl-Lovász 1986)

Statement:
Suppose n ≥ kr + (t-1)(k-1) and the edges of the complete r-uniform hypergraph
on n vertices are t-colored. Prove that some color class must contain k
pairwise disjoint edges.

Background:
- This generalizes Lovász's 1978 proof of Kneser's conjecture (k=2 case)
- Determines the chromatic number of Kneser hypergraphs: χ(KG^r(n,k)) = ⌈(n-r(k-1))/(k-1)⌉
- The proof uses topological methods (Borsuk-Ulam theorem)
- The bound is tight: a matching construction achieves it

Tags: combinatorics, hypergraphs, kneser, chromatic-number, topology, solved
-/

import Mathlib.Combinatorics.SetFamily.Intersecting
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic

namespace Erdos780

open Finset

/-!
## Part 1: Basic Definitions

Hypergraphs, colorings, and matchings.
-/

/-- An r-uniform hypergraph on vertex set α is a family of r-element subsets -/
def UniformHypergraph (α : Type*) (r : ℕ) := {S : Finset α // S.card = r}

/-- The complete r-uniform hypergraph on n vertices -/
def completeHypergraph (n r : ℕ) := {S : Finset (Fin n) // S.card = r}

/-- Two edges (hyperedges) are disjoint if they share no vertices -/
def disjointEdges {α : Type*} (e₁ e₂ : Finset α) : Prop := Disjoint e₁ e₂

/-- A set of k pairwise disjoint edges (a matching of size k) -/
def PairwiseDisjoint {α : Type*} (edges : Finset (Finset α)) : Prop :=
  ∀ e₁ ∈ edges, ∀ e₂ ∈ edges, e₁ ≠ e₂ → Disjoint e₁ e₂

/-- A t-coloring of edges -/
def EdgeColoring (n r t : ℕ) := completeHypergraph n r → Fin t

/-- A color class is the set of edges with a given color -/
def colorClass (n r t : ℕ) (c : EdgeColoring n r t) (i : Fin t) : Set (completeHypergraph n r) :=
  {e | c e = i}

/-!
## Part 2: The Kneser Hypergraph

The Kneser hypergraph KG^r(n,k) has r-subsets as vertices,
with hyperedges being k-tuples of pairwise disjoint r-sets.
-/

/-- The Kneser hypergraph KG^r(n,k): vertices are r-subsets, edges are k disjoint r-sets -/
structure KneserHypergraph (n r k : ℕ) where
  vertices : Finset (Finset (Fin n))
  vertices_uniform : ∀ S ∈ vertices, S.card = r
  edges : Finset (Finset (Finset (Fin n)))
  edges_size : ∀ E ∈ edges, E.card = k
  edges_pairwise_disjoint : ∀ E ∈ edges, PairwiseDisjoint E
  edges_from_vertices : ∀ E ∈ edges, ∀ e ∈ E, e ∈ vertices

/-- Chromatic number of the Kneser hypergraph -/
axiom chromaticNumber (n r k : ℕ) : ℕ

/-!
## Part 3: The Main Theorem (Alon-Frankl-Lovász 1986)

If n ≥ kr + (t-1)(k-1), then any t-coloring has a monochromatic matching of size k.
-/

/-- The threshold for n: n₀ = kr + (t-1)(k-1) -/
def threshold (k r t : ℕ) : ℕ := k * r + (t - 1) * (k - 1)

/-- Main theorem: n ≥ threshold implies monochromatic k-matching exists -/
axiom alon_frankl_lovasz_1986 (n r k t : ℕ) (hr : r ≥ 1) (hk : k ≥ 2) (ht : t ≥ 1)
    (hn : n ≥ threshold k r t) (c : EdgeColoring n r t) :
    ∃ i : Fin t, ∃ edges : Finset (completeHypergraph n r),
      edges.card = k ∧ PairwiseDisjoint (edges.image Subtype.val) ∧
      ∀ e ∈ edges, c e = i

/-- Equivalent formulation: chromatic number of Kneser hypergraph -/
axiom kneser_hypergraph_chromatic_number (n r k : ℕ) (hr : r ≥ 1) (hk : k ≥ 2)
    (hn : n ≥ r * k) :
    chromaticNumber n r k = Nat.ceil ((n - r * (k - 1) : ℤ) / (k - 1 : ℤ))

/-!
## Part 4: Tightness Construction

The bound is tight: n = kr - 1 + (t-1)(k-1) admits a t-coloring without k disjoint edges.
-/

/-- The tight bound: n₀ - 1 -/
def tightBound (k r t : ℕ) : ℕ := k * r - 1 + (t - 1) * (k - 1)

/-- Construction: partition [n] = X₁ ∪ X₂ ∪ ... ∪ Xₜ where |X₁| = kr-1, |Xᵢ| = k-1.
    Color by first non-empty intersection. This avoids k disjoint monochromatic edges. -/
axiom tightness_construction (k r t : ℕ) (hr : r ≥ 1) (hk : k ≥ 2) (ht : t ≥ 2) :
    let n := tightBound k r t
    ∃ c : EdgeColoring n r t,
      ∀ i : Fin t, ∀ edges : Finset (completeHypergraph n r),
        PairwiseDisjoint (edges.image Subtype.val) →
        (∀ e ∈ edges, c e = i) →
        edges.card < k

/-!
## Part 5: Special Case: Lovász's Theorem (k = 2)

The case k = 2 is Kneser's conjecture, proved by Lovász in 1978
using the Borsuk-Ulam theorem. This was the first major application
of algebraic topology to a combinatorial problem.
-/

/-- Kneser's conjecture (1955): χ(KG(n,r)) = n - 2r + 2 for n ≥ 2r -/
axiom kneser_conjecture (n r : ℕ) (hr : r ≥ 1) (hn : n ≥ 2 * r) :
    chromaticNumber n r 2 = n - 2 * r + 2

/-- The Kneser graph KG(n,r): vertices = r-subsets, edges = disjoint pairs -/
def KneserGraph (n r : ℕ) := {S : Finset (Fin n) // S.card = r}

/-- Adjacency in Kneser graph: two r-sets are adjacent iff disjoint -/
def kneserAdj (n r : ℕ) (S T : KneserGraph n r) : Prop :=
  Disjoint S.val T.val

/-!
## Part 6: Small Cases

Explicit values for small parameters.
-/

/-- KG(5,2) = Petersen graph has χ = 3 -/
axiom petersen_chromatic : chromaticNumber 5 2 2 = 3

/-- KG(7,3) has χ = 2 -/
axiom kg_7_3_chromatic : chromaticNumber 7 3 2 = 2

/-- KG(2r,r) is a matching, so χ = 2 -/
axiom kg_2r_r_chromatic (r : ℕ) (hr : r ≥ 1) : chromaticNumber (2 * r) r 2 = 2

/-- KG(2r+1,r) is an odd cycle when r = 1, odd graph when r > 1 -/
axiom kg_2r_plus_1_r (r : ℕ) (hr : r ≥ 1) : chromaticNumber (2 * r + 1) r 2 = 3

/-!
## Part 7: Connections

The Erdős-Ko-Rado theorem gives the maximum intersecting family of r-subsets,
which equals the independence number of the Kneser graph. Schrijver showed
that a vertex-critical subgraph with the same chromatic number exists.
-/

/-- Maximum intersecting family of r-subsets of [n] has size C(n-1,r-1) for n ≥ 2r -/
axiom erdos_ko_rado (n r : ℕ) (hr : r ≥ 1) (hn : n ≥ 2 * r) :
    ∃ S : Finset (Finset (Fin n)),
      (∀ A ∈ S, A.card = r) ∧
      (∀ A ∈ S, ∀ B ∈ S, (A ∩ B).Nonempty) ∧
      S.card = Nat.choose (n - 1) (r - 1)

/-!
## Part 8: Summary

Erdős Problem #780 status: SOLVED by Alon-Frankl-Lovász (1986).
-/

/-- The main result: monochromatic k-matching from t-coloring -/
theorem erdos_780_main (n r k t : ℕ) (hr : r ≥ 1) (hk : k ≥ 2) (ht : t ≥ 1)
    (hn : n ≥ threshold k r t) (c : EdgeColoring n r t) :
    ∃ i : Fin t, ∃ edges : Finset (completeHypergraph n r),
      edges.card = k ∧ PairwiseDisjoint (edges.image Subtype.val) ∧
      ∀ e ∈ edges, c e = i :=
  alon_frankl_lovasz_1986 n r k t hr hk ht hn c

/-- **Erdős Problem #780: SOLVED**

Summary combining the main theorem with tightness and Kneser's conjecture:
1. Main theorem: AFL 1986 gives monochromatic k-matching
2. Tightness: the threshold kr + (t-1)(k-1) is optimal
3. Kneser's conjecture: the k=2 case gives χ(KG(n,r)) = n - 2r + 2
-/
theorem erdos_780_summary :
    -- Main theorem holds (via AFL axiom)
    (∀ n r k t, r ≥ 1 → k ≥ 2 → t ≥ 1 → n ≥ threshold k r t →
      ∀ c : EdgeColoring n r t,
        ∃ i : Fin t, ∃ edges : Finset (completeHypergraph n r),
          edges.card = k ∧ PairwiseDisjoint (edges.image Subtype.val) ∧
          ∀ e ∈ edges, c e = i) ∧
    -- Kneser's conjecture (k=2 case)
    (∀ n r, r ≥ 1 → n ≥ 2 * r → chromaticNumber n r 2 = n - 2 * r + 2) :=
  ⟨fun n r k t hr hk ht hn c => alon_frankl_lovasz_1986 n r k t hr hk ht hn c,
   fun n r hr hn => kneser_conjecture n r hr hn⟩

end Erdos780
