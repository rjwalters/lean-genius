/-
Erdős Problem #740: Chromatic Number and Odd Cycle Avoidance

Source: https://erdosproblems.com/740
Status: OPEN (with partial results)

Statement:
Let 𝔪 be an infinite cardinal and G be a graph with chromatic number 𝔪.
Let r ≥ 1. Must G contain a subgraph of chromatic number 𝔪 which does
not contain any odd cycle of length ≤ r?

Known Results:
- Rödl proved this is true if 𝔪 = ℵ₀ and r = 3
- The general case remains OPEN

Related Questions:
- Does there exist f_r(𝔪) such that every graph with χ(G) ≥ f_r(𝔪) contains
  a subgraph with χ = 𝔪 and no odd cycles of length ≤ r?
- Same question but with girth (no cycles of any length ≤ r)

References:
- Erdős-Hajnal: Original problem formulation
- Erdős [Er81]: "On the combinatorial problems which I would most like to see solved"
- Erdős [Er95d]: "On some problems in combinatorial set theory"
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic

open Cardinal SimpleGraph

/-
**Infinite Cardinal Predicate:**
A cardinal is infinite iff it is at least ℵ₀. This is the standard characterization;
we declare it in the `Cardinal` namespace so `𝔪.IsInfinite` dot-notation resolves.
-/
namespace Cardinal

def IsInfinite (𝔪 : Cardinal) : Prop := Cardinal.aleph0 ≤ 𝔪

end Cardinal

namespace Erdos740Provable

/-
## Part I: Graph Coloring and Chromatic Number
-/

/--
**Chromatic Number:**
The minimum number of colors needed to properly color a graph G.
For infinite graphs, this is a cardinal number.
-/
noncomputable def chromaticNumber (V : Type*) (G : SimpleGraph V) : Cardinal :=
  -- The minimum cardinality k such that G is k-colorable
  Cardinal.mk V  -- placeholder

/--
**k-Colorable:**
A graph is k-colorable if vertices can be assigned colors 1..k such that
adjacent vertices have different colors.
-/
def isColorable (V : Type*) (G : SimpleGraph V) (k : Cardinal) : Prop :=
  ∃ f : V → k.out, ∀ v w : V, G.Adj v w → f v ≠ f w

/-
## Part II: Cycles in Graphs
-/

/--
**Cycle of Length n:**
A closed walk of length n with no repeated vertices, indexed cyclically by `ZMod n` so
the wraparound edge `vertices (n-1) — vertices 0` is captured automatically by `i + 1`.
-/
structure Cycle (V : Type*) (G : SimpleGraph V) (n : ℕ) where
  vertices : ZMod n → V
  edges : ∀ i : ZMod n, G.Adj (vertices i) (vertices (i + 1))
  distinct : ∀ i j : ZMod n, i ≠ j → vertices i ≠ vertices j

/--
**Odd Cycle:**
A cycle of odd length (3, 5, 7, ...).
-/
def isOddCycle (V : Type*) (G : SimpleGraph V) (n : ℕ) (c : Cycle V G n) : Prop :=
  Odd n

/--
**Triangle:**
A cycle of length 3 (the smallest odd cycle).
-/
def isTriangle (V : Type*) (G : SimpleGraph V) (c : Cycle V G 3) : Prop :=
  True

/--
**Contains Odd Cycle of Length ≤ r:**
The graph contains at least one odd cycle of length at most r.
-/
def containsOddCycleLeq (V : Type*) (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∃ n : ℕ, n ≤ r ∧ Odd n ∧ Nonempty (Cycle V G n)

/--
**No Short Odd Cycles:**
The graph contains no odd cycles of length ≤ r.
-/
def noOddCyclesLeq (V : Type*) (G : SimpleGraph V) (r : ℕ) : Prop :=
  ¬containsOddCycleLeq V G r

/--
**Triangle-Free:**
The graph contains no triangles (3-cycles).
-/
def isTriangleFree (V : Type*) (G : SimpleGraph V) : Prop :=
  noOddCyclesLeq V G 3

/-
## Part III: Subgraphs
-/

/--
**Induced Subgraph on a Subset:**
Given a subset S of vertices, the induced subgraph on S.
-/
def inducedSubgraph (V : Type*) (G : SimpleGraph V) (S : Set V) : SimpleGraph S :=
  G.induce S

/--
**Has Subgraph with Property:**
The graph contains a subgraph satisfying property P with chromatic number 𝔪.
-/
def hasSubgraphWith (V : Type*) (G : SimpleGraph V) (𝔪 : Cardinal)
    (P : ∀ S : Set V, SimpleGraph S → Prop) : Prop :=
  ∃ S : Set V, P S (inducedSubgraph V G S) ∧
    chromaticNumber S (inducedSubgraph V G S) = 𝔪

/-
## Part IV: The Erdős-Hajnal Conjecture
-/

/--
**Erdős-Hajnal Problem #740:**
If χ(G) = 𝔪 (infinite), must G have a subgraph with χ = 𝔪 and no odd cycles ≤ r?
-/
def erdosHajnalConjecture (𝔪 : Cardinal) (h𝔪 : 𝔪.IsInfinite) (r : ℕ) : Prop :=
  ∀ V : Type*, ∀ G : SimpleGraph V,
    chromaticNumber V G = 𝔪 →
      ∃ S : Set V,
        chromaticNumber S (inducedSubgraph V G S) = 𝔪 ∧
        noOddCyclesLeq S (inducedSubgraph V G S) r

/--
**Special Case: r = 3 (Triangle-Free):**
Must every graph with χ = 𝔪 contain a triangle-free subgraph with χ = 𝔪?
-/
def triangleFreeConjecture (𝔪 : Cardinal) (h𝔪 : 𝔪.IsInfinite) : Prop :=
  erdosHajnalConjecture 𝔪 h𝔪 3

/--
**Countably Infinite Case:**
The conjecture for 𝔪 = ℵ₀.
-/
def countableCase (r : ℕ) : Prop :=
  ∀ V : Type*, ∀ G : SimpleGraph V,
    chromaticNumber V G = Cardinal.aleph0 →
      ∃ S : Set V,
        chromaticNumber S (inducedSubgraph V G S) = Cardinal.aleph0 ∧
        noOddCyclesLeq S (inducedSubgraph V G S) r

/-
## Part V: Rödl's Theorem
-/

/--
**Rödl's Theorem:**
The conjecture holds for 𝔪 = ℵ₀ and r = 3.
Every countably chromatic graph contains a triangle-free subgraph with χ = ℵ₀.
-/
theorem rodl_theorem : countableCase 3 := by sorry

/--
**Corollary: Countable Triangle-Free Case:**
From Rödl's theorem, the triangle-free case is resolved for countable chromatic number.
-/
theorem countable_triangle_free : countableCase 3 := rodl_theorem

/-
## Part VI: The General Function f_r(𝔪)
-/

/--
**Threshold Function Conjecture:**
Does there exist f_r(𝔪) such that χ(G) ≥ f_r(𝔪) implies G has a subgraph
with χ = 𝔪 and no odd cycles ≤ r?
-/
def thresholdFunctionExists (𝔪 : Cardinal) (r : ℕ) : Prop :=
  ∃ f : Cardinal,
    ∀ V : Type*, ∀ G : SimpleGraph V,
      chromaticNumber V G ≥ f →
        ∃ S : Set V,
          chromaticNumber S (inducedSubgraph V G S) = 𝔪 ∧
          noOddCyclesLeq S (inducedSubgraph V G S) r

/--
**Open Problem:**
The existence of f_r(𝔪) is unknown for most cases.
-/
def thresholdFunctionOpen : Prop :=
  ¬∀ 𝔪 : Cardinal.{0}, ∀ r : ℕ, 𝔪.IsInfinite →
    thresholdFunctionExists 𝔪 r ∨ ¬thresholdFunctionExists 𝔪 r

/-
## Part VII: Girth Variant
-/

/--
**Girth:**
The length of the shortest cycle in G (or ∞ if G is a forest).
-/
noncomputable def girth (V : Type*) (G : SimpleGraph V) : ℕ∞ :=
  -- The minimum cycle length, or ⊤ if acyclic
  0  -- placeholder

/--
**No Cycles ≤ r:**
The graph has girth > r (no cycles of any length ≤ r).
-/
def girthGreaterThan (V : Type*) (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ n : ℕ, n ≤ r → IsEmpty (Cycle V G n)

/--
**Girth Variant Conjecture:**
Must G with χ = 𝔪 contain a subgraph with χ = 𝔪 and girth > r?
This is stronger than the odd cycle version.
-/
def girthConjecture (𝔪 : Cardinal) (h𝔪 : 𝔪.IsInfinite) (r : ℕ) : Prop :=
  ∀ V : Type*, ∀ G : SimpleGraph V,
    chromaticNumber V G = 𝔪 →
      ∃ S : Set V,
        chromaticNumber S (inducedSubgraph V G S) = 𝔪 ∧
        girthGreaterThan S (inducedSubgraph V G S) r

/--
**Girth implies Odd Cycle:**
The girth conjecture implies the odd cycle conjecture.
-/
theorem girth_implies_odd (𝔪 : Cardinal) (h𝔪 : 𝔪.IsInfinite) (r : ℕ) :
    girthConjecture 𝔪 h𝔪 r → erdosHajnalConjecture 𝔪 h𝔪 r := by
  intro hGirth V G hχ
  obtain ⟨S, hS, hGirthS⟩ := hGirth V G hχ
  use S
  constructor
  · exact hS
  · -- No cycles ≤ r implies no odd cycles ≤ r
    intro ⟨n, hn, hOdd, hCycle⟩
    exact (hGirthS n hn).false hCycle.some

/-
## Part VIII: Finite Analogs
-/

/--
**Finite Analog:**
For finite graphs, given χ(G) = n, find subgraph with χ = k and no odd cycles ≤ r.
-/
def finiteAnalog (n k r : ℕ) : Prop :=
  ∀ V : Type*, ∀ G : SimpleGraph V, [Fintype V] →
    (∃ m : ℕ, chromaticNumber V G = m ∧ m ≥ n) →
      ∃ S : Set V,
        (∃ j : ℕ, chromaticNumber S (inducedSubgraph V G S) = j ∧ j ≥ k) ∧
        noOddCyclesLeq S (inducedSubgraph V G S) r

/--
**Finite r = 3 Case:**
The finite version with r = 3 has been studied.
-/
theorem finite_triangle_free_progress :
    ∃ c : ℕ, finiteAnalog c 3 3 := by sorry

/-
## Part IX: Bipartite Subgraphs
-/

/--
**Bipartite Graph:**
A graph with no odd cycles at all (χ ≤ 2).
-/
def isBipartite (V : Type*) (G : SimpleGraph V) : Prop :=
  ∀ n : ℕ, Odd n → IsEmpty (Cycle V G n)

/--
**Bipartite Subgraph:**
For r = ∞, we ask: must G with χ = 𝔪 contain a bipartite subgraph with χ = 𝔪?
Answer: NO! A bipartite graph has χ ≤ 2.
-/
theorem no_infinite_bipartite :
    ∀ 𝔪 : Cardinal, 𝔪 > 2 →
      ¬∀ V : Type*, ∀ G : SimpleGraph V,
        chromaticNumber V G = 𝔪 →
          ∃ S : Set V,
            chromaticNumber S (inducedSubgraph V G S) = 𝔪 ∧
            isBipartite S (inducedSubgraph V G S) := by
  intro 𝔪 h𝔪 hContra
  -- A bipartite graph has chromatic number at most 2
  -- So it can't have chromatic number 𝔪 > 2
  sorry

/-
## Part X: Summary
-/

/--
**Problem Status Summary:**
- Rödl proved the case 𝔪 = ℵ₀, r = 3
- The general case remains OPEN
- The girth variant is also open
-/
theorem erdos_740_summary :
    (-- Rödl's theorem
     countableCase 3) ∧
    (-- Girth implies odd cycle
     ∀ 𝔪 h𝔪 r, girthConjecture 𝔪 h𝔪 r → erdosHajnalConjecture 𝔪 h𝔪 r) ∧
    (-- Bipartite version fails for 𝔪 > 2
     ∀ 𝔪, 𝔪 > 2 → ¬∀ V G, chromaticNumber V G = 𝔪 →
       ∃ S : Set V, chromaticNumber S (inducedSubgraph V G S) = 𝔪 ∧
         isBipartite S (inducedSubgraph V G S)) := by
  exact ⟨rodl_theorem, girth_implies_odd, no_infinite_bipartite⟩

/--
**Main Theorem:**
Erdős Problem #740 is OPEN, but Rödl resolved the countable r = 3 case.
-/
theorem erdos_740 : countableCase 3 := rodl_theorem

/--
**Open Question:**
Does the conjecture hold for all infinite cardinals and all r?
-/
def openQuestion (𝔪 : Cardinal) (h𝔪 : 𝔪.IsInfinite) (r : ℕ) : Prop :=
  erdosHajnalConjecture 𝔪 h𝔪 r

/--
**Erdős's Most Wanted:**
In [Er81], Erdős listed this among problems he "would most like to see solved."
-/
def erdosMostWanted : Prop :=
  ∀ 𝔪 : Cardinal.{0}, ∀ h𝔪 : 𝔪.IsInfinite,
    ∀ r : ℕ, r ≥ 1 →
      erdosHajnalConjecture 𝔪 h𝔪 r

end Erdos740Provable
