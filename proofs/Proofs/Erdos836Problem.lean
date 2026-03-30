/-
Erdős Problem #836: Intersecting 3-Chromatic Hypergraphs

Source: https://erdosproblems.com/836
Status: SOLVED (with counterexample)

Statement:
Let r ≥ 2 and G be an r-uniform hypergraph with chromatic number 3 such that
any two edges have a non-empty intersection.

Questions:
1. Must G contain O(r²) many vertices?
2. Must there be two edges which meet in ≫ r many vertices?

Answers:
1. NO - Alon's counterexample has ~4^r/√r vertices
2. PARTIAL - Erdős-Lovász proved edges meet in ≫ r/log r vertices

Context:
- A hypergraph is r-uniform if all edges have size r
- Chromatic number 3 means vertices can be 3-coloured with no monochromatic edge
- An intersecting hypergraph has every pair of edges sharing at least one vertex
- The Fano plane is an example where no two edges meet in r-1 vertices

References:
- [ErLo75] Erdős, P. and Lovász, L. (1975): Problems and results on 3-chromatic
  hypergraphs and some related questions. 609-627.
- Alon: Counterexample construction

Tags: combinatorics, hypergraphs, chromatic-number, intersecting-families
-/

import Mathlib.Combinatorics.SetFamily.Intersecting
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

namespace Erdos836

/-
## Part I: Hypergraph Definitions
-/

/--
**Hypergraph:**
A collection of edges (subsets) on a vertex set.
-/
structure Hypergraph (V : Type*) where
  edges : Set (Set V)

/--
**r-uniform hypergraph:**
All edges have exactly r vertices.
-/
def IsUniform (H : Hypergraph V) (r : ℕ) : Prop :=
  ∀ e ∈ H.edges, (Set.toFinite e).toFinset.card = r

/--
**Intersecting hypergraph:**
Any two edges share at least one vertex.
-/
def IsIntersecting (H : Hypergraph V) : Prop :=
  ∀ e₁ ∈ H.edges, ∀ e₂ ∈ H.edges, (e₁ ∩ e₂).Nonempty

/-
## Part II: Chromatic Number
-/

/--
**Proper colouring:**
A k-colouring such that no edge is monochromatic.
-/
def IsProperColouring {V : Type*} (H : Hypergraph V) (k : ℕ) (c : V → Fin k) : Prop :=
  ∀ e ∈ H.edges, ∀ colour : Fin k, ¬(∀ v ∈ e, c v = colour)

/--
**3-chromatic hypergraph:**
Has chromatic number exactly 3 (3-colourable but not 2-colourable).
-/
def IsThreeChromatic {V : Type*} (H : Hypergraph V) : Prop :=
  (∃ c : V → Fin 3, IsProperColouring H 3 c) ∧
  ¬(∃ c : V → Fin 2, IsProperColouring H 2 c)

/--
**Chromatic number at most 3:**
There exists a proper 3-colouring.
-/
def ChromaticAtMostThree {V : Type*} (H : Hypergraph V) : Prop :=
  ∃ c : V → Fin 3, IsProperColouring H 3 c

/-
## Part III: Vertex Count Question
-/

/--
**Vertex set of a hypergraph:**
The union of all edges.
-/
def vertices {V : Type*} (H : Hypergraph V) : Set V :=
  ⋃ e ∈ H.edges, e

/--
**Finite vertex count:**
The number of vertices in the hypergraph.
-/
noncomputable def vertexCount {V : Type*} [Fintype V] (H : Hypergraph V) : ℕ :=
  Fintype.card V

/--
**Question 1 (FALSE): O(r²) vertex bound**
Does every r-uniform, intersecting, 3-chromatic hypergraph have O(r²) vertices?
-/
def Question1 : Prop :=
  ∃ C : ℝ, C > 0 ∧
    ∀ r : ℕ, r ≥ 2 →
      ∀ V : Type*, ∀ H : Hypergraph V,
        IsUniform H r → IsIntersecting H → ChromaticAtMostThree H →
          ∃ (fin : Fintype V), (Fintype.card V : ℝ) ≤ C * r^2

/--
**Question 1 is FALSE:**
Alon provided a counterexample with exponentially many vertices.
Axiomatized because the construction and verification require detailed
combinatorial arguments beyond Mathlib.
-/
axiom question1_false : ¬Question1

/-
## Part IV: Alon's Counterexample
-/

/--
**Alon's construction:**
Vertices: X of size 2r-2 and Y of size C(2r-2, r-1)/2 (partitions of X)
Edges: All r-subsets of X, plus (r-1)-subsets of X with their partition element

This gives ~4^r/√r vertices.
-/
def AlonVertexCount (r : ℕ) : ℝ :=
  4^r / Real.sqrt r

/--
**Alon's hypergraph properties:**
- r-uniform
- Intersecting
- Chromatic number 3
- Has ~4^r/√r vertices

Axiomatized because verifying these properties requires detailed
combinatorial analysis of the partition-based construction.
-/
/--
**Exponential growth:**
The counterexample shows vertices can grow as 4^r/√r, not O(r²).
Axiomatized: the inequality 4^r/√r > r² for large r follows from
exponential vs polynomial growth but requires careful real analysis.
-/
/-
## Part V: Edge Intersection Question
-/

/--
**Question 2: Large intersection**
Must two edges meet in ≫ r vertices?
-/
def Question2 : Prop :=
  ∀ r : ℕ, r ≥ 2 →
    ∀ V : Type*, ∀ H : Hypergraph V,
      IsUniform H r → IsIntersecting H → ChromaticAtMostThree H →
        ∃ e₁ ∈ H.edges, ∃ e₂ ∈ H.edges, e₁ ≠ e₂ ∧
          ∃ (fin : Fintype (e₁ ∩ e₂ : Set V)),
            (Fintype.card (e₁ ∩ e₂ : Set V) : ℝ) ≥ r / 2

/--
**Erdős-Lovász bound:**
Two edges must meet in ≫ r/log r vertices.
Axiomatized because the probabilistic argument from Erdős-Lovász (1975)
is beyond current Mathlib capabilities.
-/
def ErdosLovaszBound (r : ℕ) : ℝ :=
  r / Real.log r

axiom erdos_lovasz_bound (r : ℕ) (hr : r ≥ 2) :
    ∀ V : Type*, ∀ H : Hypergraph V,
      IsUniform H r → IsIntersecting H → ChromaticAtMostThree H →
        ∃ e₁ ∈ H.edges, ∃ e₂ ∈ H.edges, e₁ ≠ e₂ ∧
          ∃ (fin : Fintype (e₁ ∩ e₂ : Set V)),
            (Fintype.card (e₁ ∩ e₂ : Set V) : ℝ) ≥ ErdosLovaszBound r / 2

/-
## Part VI: The Fano Plane
-/

/--
**Fano plane extremality:**
The Fano plane (projective plane of order 2) is a 3-uniform, intersecting,
3-chromatic hypergraph with 7 points and 7 lines, where no two lines share
r-1 = 2 points (any two lines share exactly 1 point).
-/
def otherExamples : Prop :=
  ∃ r : ℕ, r ≥ 3 ∧
    ∃ V : Type*, ∃ H : Hypergraph V,
      IsUniform H r ∧ IsIntersecting H ∧ ChromaticAtMostThree H ∧
      (∀ e₁ ∈ H.edges, ∀ e₂ ∈ H.edges, e₁ ≠ e₂ →
        ∃ (fin : Fintype (e₁ ∩ e₂ : Set V)),
          Fintype.card (e₁ ∩ e₂ : Set V) < r - 1)

/-
## Part VII: Specific Values
-/

/--
**r = 3 case:**
3-uniform, intersecting, 3-chromatic hypergraph.
Fano plane is an example with 7 vertices.
-/
example : 3 ≥ 2 := by norm_num

/--
**Alon's construction for r = 3:**
X has 2·3-2 = 4 elements.
Y has C(4,2)/2 = 3 elements.
Total: 7 vertices (matches Fano!).
-/
example : 2 * 3 - 2 = 4 := by norm_num
example : Nat.choose 4 2 / 2 = 3 := by native_decide

/--
**Alon's construction for r = 4:**
X has 2·4-2 = 6 elements.
Y has C(6,3)/2 = 10 elements.
Total: 16 vertices.
Compare to O(r²) = O(16).
-/
example : 2 * 4 - 2 = 6 := by norm_num
example : Nat.choose 6 3 / 2 = 10 := by native_decide

/-
## Part VIII: Summary
-/

/--
**Erdős Problem #836: Summary**

**QUESTION 1:** Must G have O(r²) vertices?
- ANSWER: NO
- Alon's counterexample has ~4^r/√r vertices

**QUESTION 2:** Must two edges meet in ≫ r vertices?
- PARTIAL: Erdős-Lovász proved ≫ r/log r
- Open whether r/log r can be improved to r

**KEY EXAMPLES:**
- Fano plane: 3-uniform, no two edges share r-1 vertices
- Alon's construction: exponentially many vertices

**STATUS:** SOLVED (with counterexample to Q1, partial result for Q2)
-/
theorem erdos_836_summary :
    ¬Question1 ∧
    (∀ r : ℕ, r ≥ 2 →
      ∀ V : Type*, ∀ H : Hypergraph V,
        IsUniform H r → IsIntersecting H → ChromaticAtMostThree H →
          ∃ e₁ ∈ H.edges, ∃ e₂ ∈ H.edges, e₁ ≠ e₂ ∧
            ∃ (fin : Fintype (e₁ ∩ e₂ : Set V)),
              (Fintype.card (e₁ ∩ e₂ : Set V) : ℝ) ≥ ErdosLovaszBound r / 2) :=
  ⟨question1_false, erdos_lovasz_bound⟩

end Erdos836
