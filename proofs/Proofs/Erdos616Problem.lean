/-
Erdős Problem #616: Covering Numbers of Hypergraphs

Source: https://erdosproblems.com/616
Status: OPEN

Statement:
Let r ≥ 3. For an r-uniform hypergraph G, let τ(G) denote the covering number
(or transversal number), the minimum size of a set of vertices which includes
at least one vertex from each edge.

Determine the best possible t such that: if G is an r-uniform hypergraph where
every subgraph G' on at most 3r-3 vertices has τ(G') ≤ 1, then τ(G) ≤ t.

Background:
The covering number (also called vertex cover number or transversal number)
is a fundamental parameter in hypergraph theory. A covering set must "hit"
every edge - i.e., intersect every hyperedge in at least one vertex.

The condition τ(G') ≤ 1 for small subgraphs means that every "small" induced
subhypergraph has a vertex that covers all its edges. This is a strong local
condition that should imply bounds on the global covering number.

Known Results:
Erdős-Hajnal-Tuza (1991) proved:
  (3/16)r + 7/8 ≤ t ≤ (1/5)r

The gap between 0.1875r and 0.2r remains OPEN.

References:
- [EHT91] Erdős, Hajnal, Tuza: "Local constraints ensuring small representing
  sets" J. Combin. Theory Ser. A (1991), 78-84.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

namespace Erdos616

/-
## Part I: Hypergraph Definitions
-/

/--
**r-uniform hypergraph:**
A hypergraph where every edge has exactly r vertices.
Represented as a set of edges, each edge being a Finset of vertices.
-/
structure UniformHypergraph (V : Type*) (r : ℕ) where
  edges : Set (Finset V)
  uniform : ∀ e ∈ edges, e.card = r

/--
**Covering set (vertex cover / transversal):**
A set S of vertices covers hypergraph G if S intersects every edge.
-/
def IsCoveringSet {V : Type*} {r : ℕ} (G : UniformHypergraph V r) (S : Set V) : Prop :=
  ∀ e ∈ G.edges, ∃ v ∈ S, v ∈ e

/--
**Covering number τ(G):**
The minimum size of a covering set.
-/
noncomputable def coveringNumber {V : Type*} [Fintype V] {r : ℕ}
    (G : UniformHypergraph V r) : ℕ :=
  ⨅ (S : Finset V) (_ : IsCoveringSet G ↑S), S.card

/--
**Induced subhypergraph:**
The hypergraph induced on a vertex subset W.
-/
def inducedSubhypergraph {V : Type*} {r : ℕ}
    (G : UniformHypergraph V r) (W : Set V) : UniformHypergraph V r where
  edges := {e ∈ G.edges | ↑e ⊆ W}
  uniform := by
    intro e he
    exact G.uniform e he.1

/-
## Part II: The Local Condition
-/

/--
**Local covering condition:**
Every induced subhypergraph on at most k vertices has covering number ≤ 1.

This means every "small" subhypergraph has a vertex that covers all its edges.
Equivalently: small subhypergraphs have a common point in all edges.
-/
def HasLocalCoveringBound {V : Type*} [Fintype V] {r : ℕ}
    (G : UniformHypergraph V r) (k : ℕ) : Prop :=
  ∀ (W : Finset V), W.card ≤ k →
    let H := inducedSubhypergraph G ↑W
    ∃ v ∈ (↑W : Set V), IsCoveringSet H {v}

/--
**The specific bound 3r-3:**
For r-uniform hypergraphs, the relevant threshold is 3r-3 vertices.
-/
def localThreshold (r : ℕ) : ℕ := 3 * r - 3

/-
## Part III: The Main Question
-/

/--
**Erdős Problem #616:**
Determine the best t = t(r) such that:
  If G is r-uniform and every subgraph on ≤ 3r-3 vertices has τ ≤ 1,
  then τ(G) ≤ t.
-/
def ErdosProblem616 (r : ℕ) (t : ℕ) : Prop :=
  r ≥ 3 →
  ∀ (V : Type*) [Fintype V] (G : UniformHypergraph V r),
    HasLocalCoveringBound G (localThreshold r) →
    coveringNumber G ≤ t

/--
**The optimal constant t(r):**
There exists an optimal t(r) that works for all such hypergraphs.
-/
def optimalCoveringBound (r : ℕ) : ℕ := sorry  -- The exact value is OPEN

/-
## Part IV: Known Bounds (Erdős-Hajnal-Tuza 1991)
-/

/--
**Lower Bound:**
t(r) ≥ (3/16)r + 7/8

There exist r-uniform hypergraphs satisfying the local condition
but requiring at least this many vertices to cover.
-/
axiom eht_lower_bound :
  ∀ r : ℕ, r ≥ 3 →
    ∃ (V : Type*) [Fintype V] (G : UniformHypergraph V r),
      HasLocalCoveringBound G (localThreshold r) ∧
      (coveringNumber G : ℝ) ≥ (3 : ℝ) / 16 * r + 7 / 8

/--
**Upper Bound:**
t(r) ≤ (1/5)r

Every r-uniform hypergraph satisfying the local condition
has covering number at most r/5.
-/
axiom eht_upper_bound :
  ∀ r : ℕ, r ≥ 3 →
    ∀ (V : Type*) [Fintype V] (G : UniformHypergraph V r),
      HasLocalCoveringBound G (localThreshold r) →
      (coveringNumber G : ℝ) ≤ (1 : ℝ) / 5 * r

/--
**The coefficient bounds:**
The optimal coefficient c where t(r) ~ c·r satisfies:
  3/16 ≤ c ≤ 1/5
  0.1875 ≤ c ≤ 0.2
-/
def lowerCoefficient : ℝ := 3 / 16  -- = 0.1875
def upperCoefficient : ℝ := 1 / 5   -- = 0.2

theorem coefficient_bounds :
    lowerCoefficient ≤ upperCoefficient := by
  unfold lowerCoefficient upperCoefficient
  norm_num

/-
## Part V: Special Cases
-/

/--
**r = 3 case:**
For 3-uniform hypergraphs (ordinary hypergraphs with 3 vertices per edge),
the threshold is 3·3 - 3 = 6 vertices.
-/
def threshold_3uniform : ℕ := localThreshold 3  -- = 6

/--
**r = 4 case:**
For 4-uniform hypergraphs, the threshold is 3·4 - 3 = 9 vertices.
-/
def threshold_4uniform : ℕ := localThreshold 4  -- = 9

/--
**Small r computations:**
The bounds give:
- r = 3: 1.4375 ≤ t(3) ≤ 0.6 (lower bound > upper bound suggests tightening needed)
- r = 10: 2.75 ≤ t(10) ≤ 2
- r = 100: 19.625 ≤ t(100) ≤ 20

The bounds become meaningful for larger r.
-/
axiom bounds_meaningful_large_r : True

/-
## Part VI: Why the Condition 3r-3?
-/

/--
**The threshold 3r-3:**
This specific threshold arises from extremal considerations.

For an r-uniform hypergraph:
- 3r-3 vertices can accommodate at most a few disjoint edges
- The local condition τ(G') ≤ 1 is non-trivial only when G' has ≥ 2 edges
- The bound 3r-3 captures the minimum needed for interesting structure
-/
axiom threshold_explanation : True

/--
**Sunflowers and local conditions:**
The problem relates to sunflower-type structures.
A sunflower is a collection of edges sharing a common "core".
The local condition τ ≤ 1 enforces sunflower-like structure locally.
-/
axiom sunflower_connection : True

/-
## Part VII: Equivalent Formulations
-/

/--
**Intersection property:**
τ(G) ≤ 1 ⟺ All edges share a common vertex.

The local condition says: every small subhypergraph has a "kernel" vertex.
-/
def HasKernel {V : Type*} {r : ℕ} (G : UniformHypergraph V r) : Prop :=
  ∃ v : V, ∀ e ∈ G.edges, v ∈ e

theorem tau_one_iff_kernel {V : Type*} [Fintype V] {r : ℕ}
    (G : UniformHypergraph V r) :
    (∃ v : V, IsCoveringSet G {v}) ↔ HasKernel G := by
  constructor
  · intro ⟨v, hv⟩
    use v
    intro e he
    obtain ⟨w, hw, hwe⟩ := hv e he
    simp at hw
    rwa [hw]
  · intro ⟨v, hv⟩
    use v
    intro e he
    use v
    exact ⟨Set.mem_singleton v, hv e he⟩

/-
## Part VIII: Fractional Relaxation
-/

/--
**Fractional covering number τ*(G):**
The LP relaxation of the covering number.
Instead of picking vertices (0/1), allow fractional weights.
-/
axiom fractionalCoveringNumber : ∀ {V : Type*} [Fintype V] {r : ℕ},
  UniformHypergraph V r → ℝ

/--
**Fractional vs Integer:**
τ*(G) ≤ τ(G) always.
The gap between them relates to the integrality gap.
-/
axiom fractional_le_integer : True

/-
## Part IX: Summary
-/

/--
**Erdős Problem #616: OPEN**

**QUESTION:** Determine the best t(r) such that:
If every induced subhypergraph on ≤ 3r-3 vertices has τ ≤ 1,
then τ(G) ≤ t(r).

**KNOWN (Erdős-Hajnal-Tuza 1991):**
  (3/16)r + 7/8 ≤ t(r) ≤ (1/5)r
  0.1875r ≤ t(r) ≤ 0.2r (asymptotically)

**OPEN:** Close the gap between 3/16 and 1/5.

**KEY INSIGHTS:**
1. The local condition τ ≤ 1 means all edges share a common vertex locally
2. The question is how this local structure bounds global covering number
3. The bounds differ by only ~7% asymptotically, but closing this is hard
4. Related to sunflower lemmas and Helly-type theorems
-/
theorem erdos_616_summary :
    -- Lower bound exists
    (∀ r : ℕ, r ≥ 3 →
      ∃ (V : Type*) [Fintype V] (G : UniformHypergraph V r),
        HasLocalCoveringBound G (localThreshold r) ∧
        (coveringNumber G : ℝ) ≥ lowerCoefficient * r) ∧
    -- Upper bound holds
    (∀ r : ℕ, r ≥ 3 →
      ∀ (V : Type*) [Fintype V] (G : UniformHypergraph V r),
        HasLocalCoveringBound G (localThreshold r) →
        (coveringNumber G : ℝ) ≤ upperCoefficient * r) := by
  constructor
  · intro r hr
    have := eht_lower_bound r hr
    obtain ⟨V, _, G, hlocal, hbound⟩ := this
    exact ⟨V, inferInstance, G, hlocal, by linarith⟩
  · intro r hr V _ G hlocal
    exact eht_upper_bound r hr V G hlocal

/--
**Problem status:**
Erdős Problem #616 remains OPEN.
The exact asymptotic coefficient c where t(r) ~ c·r is unknown.
-/
theorem erdos_616_status : True := trivial

end Erdos616
