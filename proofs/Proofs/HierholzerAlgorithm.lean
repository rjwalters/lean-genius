/-
Hierholzer's Algorithm: Constructive Eulerian Path Finding

This file formalizes key components of Hierholzer's algorithm for finding
Eulerian paths and circuits in graphs, building on Mathlib's SimpleGraph
infrastructure.

The main contributions are:
1. The existence direction of Euler's theorem (connected + all even degrees → Eulerian circuit)
2. Properties of Eulerian walks (edge count, positive length)
3. Generalized impossibility (≥4 odd vertices → no Eulerian path)
4. Concrete K₃ example with Eulerian circuit construction
5. **Circuit removal preserves even degrees** (key Hierholzer invariant, PROVED)

Authors: lean-genius research (researcher-1, researcher-2)
-/
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.NormNum

namespace HierholzerAlgorithm

open SimpleGraph

/-
## Part 1: Euler's Theorem - Existence Direction

The existence direction: a connected graph where every vertex has even degree
admits an Eulerian circuit. This is the converse of Mathlib's
`Walk.IsEulerian.card_odd_degree` theorem.

Mathlib's SimpleGraph.Trails module contains an explicit TODO for this result.
We state it as an axiom and build infrastructure around it.
-/

section EulerExistence

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Euler's Circuit Theorem (Existence Direction)**:
    A connected graph with all even degrees has an Eulerian circuit.

    This is the converse of the necessity direction proved in Mathlib
    (`Walk.IsEulerian.card_odd_degree`). The proof would proceed by
    Hierholzer's algorithm:
    1. Start at any vertex, greedily walk until returning to start
    2. If unused edges remain at a vertex on the circuit, recurse
    3. Splice sub-circuits into the main circuit
    Termination follows from strict decrease in edge count. -/
axiom euler_circuit_exists
    (hconn : G.Connected)
    (heven : ∀ v : V, Even (G.degree v)) :
    ∃ v : V, ∃ p : G.Walk v v, p.IsEulerian

/-- **Euler's Trail Theorem (Existence Direction)**:
    A connected graph with exactly two odd-degree vertices u, v has an
    Eulerian trail from u to v. -/
axiom euler_trail_exists {u v : V}
    (hconn : G.Connected)
    (huv : u ≠ v)
    (hodd_u : Odd (G.degree u))
    (hodd_v : Odd (G.degree v))
    (heven : ∀ w : V, w ≠ u → w ≠ v → Even (G.degree w)) :
    ∃ p : G.Walk u v, p.IsEulerian

end EulerExistence

/-
## Part 2: Properties of Eulerian Walks

Proved results about Eulerian walk structure.
-/

section EulerianProperties

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An Eulerian walk's edge list has the same elements as the graph's edge set. -/
theorem eulerian_edges_toFinset_eq {u v : V} (p : G.Walk u v) (hp : p.IsEulerian) :
    p.edges.toFinset = G.edgeFinset := by
  ext e
  simp only [List.mem_toFinset, mem_edgeFinset]
  constructor
  · intro he; exact p.edges_subset_edgeSet he
  · intro he
    have hcount := hp e he
    exact List.count_pos_iff.mp (by omega)

/-- An Eulerian walk has as many edges as the graph. -/
theorem eulerian_edges_length {u v : V} (p : G.Walk u v) (hp : p.IsEulerian) :
    p.edges.length = G.edgeFinset.card := by
  have hnodup := hp.isTrail.edges_nodup
  have heq := eulerian_edges_toFinset_eq G p hp
  rw [← heq]
  exact (List.toFinset_card_of_nodup hnodup).symm

/-- An Eulerian circuit in a nonempty graph has positive edge count. -/
theorem eulerian_pos_edges
    {u : V} (p : G.Walk u u) (hp : p.IsEulerian)
    (hne : G.edgeFinset.Nonempty) :
    0 < p.edges.length := by
  rw [eulerian_edges_length G p hp]
  exact Finset.card_pos.mpr hne

/-- **No Eulerian Path with ≥4 Odd Vertices**:
    Generalizes the Königsberg impossibility to any graph with 4+ odd-degree vertices. -/
theorem no_eulerian_of_four_odd
    (hodd : 4 ≤ Fintype.card {v : V | Odd (G.degree v)}) :
    ∀ (u v : V) (p : G.Walk u v), ¬p.IsEulerian := by
  intro u v p hp
  have h := hp.card_odd_degree
  omega

/-- An Eulerian circuit implies all vertices have even degree. -/
theorem euler_circuit_all_even {u : V}
    (p : G.Walk u u) (hp : p.IsEulerian) (v : V) :
    Even (G.degree v) := by
  have hiff := hp.even_degree_iff (x := v)
  rw [show (u ≠ u) = False from by simp] at hiff
  simp only [false_implies] at hiff
  exact hiff.mpr trivial

end EulerianProperties

/-
## Part 3: Hierholzer's Cycle-Splicing Infrastructure

The key invariant for Hierholzer: removing a circuit from a graph with
all-even degrees preserves the all-even-degrees property.

**This section converts the former axiom to a proved theorem.**

Proof strategy:
1. `Walk.IsTrail.even_countP_edges_iff` (Mathlib): for a closed trail,
   the count of edges incident to each vertex is even.
2. The degree in G.deleteEdges equals the original degree minus the count
   of removed incident edges (proved via neighborFinset filter partition).
3. Even minus even is even.
-/

section CycleSplicing

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- For a closed trail, the number of edges incident to each vertex is even.
    This follows directly from `Walk.IsTrail.even_countP_edges_iff` with u = v,
    making the RHS vacuously true. -/
lemma closed_trail_even_countP
    {u : V} (p : G.Walk u u) (hp : p.IsTrail) (x : V) :
    Even (p.edges.countP (fun e => x ∈ e)) :=
  (hp.even_countP_edges_iff x).mpr (fun h => absurd rfl h)

/-- Degree decomposition: The degree of v in G equals the degree of v in
    (G.deleteEdges S) plus the number of neighbors of v whose edge is in S.
    Uses the filter-complement partition of the neighbor finset. -/
lemma degree_eq_deleteEdges_add (v : V)
    (S : Set (Sym2 V)) [DecidablePred (· ∈ S)] :
    G.degree v = (G.deleteEdges S).degree v +
      ((G.neighborFinset v).filter (fun w => s(v, w) ∈ S)).card := by
  -- Rewrite both degrees in terms of neighborFinset
  have h1 : (G.deleteEdges S).neighborFinset v =
      (G.neighborFinset v).filter (fun w => s(v, w) ∉ S) := by
    ext w
    simp [mem_neighborFinset, deleteEdges_adj]
  simp only [SimpleGraph.degree, h1]
  exact (Finset.filter_card_add_filter_neg_card_eq_card (fun w => s(v, w) ∈ S)).symm

/-- The number of deleted neighbors of v (neighbors w such that s(v,w) is in the
    trail's edge set) equals the countP of trail edges incident to v.

    The proof establishes a bijection between:
    - {w ∈ neighborFinset(v) | s(v,w) ∈ trail edges}
    - edges in the trail incident to v (counted by countP)

    Key steps:
    1. For a nodup list, countP equals the length of the filtered list
    2. The filtered list length equals the filtered toFinset card (nodup)
    3. The filtered toFinset bijects with the deleted neighbor finset -/
lemma deleted_neighbors_eq_countP
    {u w : V} (p : G.Walk u w) (hp : p.IsTrail) (v : V) :
    ((G.neighborFinset v).filter (fun x => s(v, x) ∈
      (p.edges.toFinset : Set (Sym2 V)))).card =
      p.edges.countP (fun e => v ∈ e) := by
  have hnodup := hp.edges_nodup
  -- countP on a list = length of filter
  rw [← List.countP_eq_length_filter]
  -- For a nodup list, (l.filter p).length = (l.toFinset.filter p).card
  rw [show (p.edges.filter (fun e => v ∈ e)).length =
      (p.edges.toFinset.filter (fun e => v ∈ e)).card from by
    rw [← List.toFinset_card_of_nodup (hnodup.filter _)]
    congr 1; ext e; simp [List.mem_toFinset]]
  -- Now show |{x ∈ nbrFinset v | s(v,x) ∈ trail.toFinset}| = |trail.toFinset.filter (v ∈ ·)|
  -- via the bijection x ↦ s(v,x)
  apply Finset.card_nbij (fun x => s(v, x))
  · -- MapsTo: if x is a neighbor with s(v,x) in trail, then s(v,x) ∈ trail.filter(v ∈ ·)
    intro x hx
    simp only [Finset.mem_filter, Set.mem_coe, List.mem_toFinset] at hx ⊢
    exact ⟨hx.2, Sym2.mem_mk_left v x⟩
  · -- Injective: s(v,x₁) = s(v,x₂) implies x₁ = x₂ (using looplessness of G)
    intro x₁ hx₁ x₂ _ heq
    simp only [Finset.mem_filter, mem_neighborFinset] at hx₁
    rcases Sym2.eq_iff.mp heq with ⟨_, h⟩ | ⟨h₁, _⟩
    · exact h
    · rw [h₁] at hx₁; exact absurd rfl (G.ne_of_adj hx₁.1)
  · -- Surjective: every e ∈ trail.toFinset with v ∈ e has form s(v,x) for neighbor x
    intro e he
    simp only [Finset.mem_filter, List.mem_toFinset] at he
    obtain ⟨hmem, hv⟩ := he
    have hedge : e ∈ G.edgeSet := p.edges_subset_edgeSet hmem
    revert hv hedge hmem
    refine Sym2.ind (fun a b => ?_) e
    intro hmem hedge hv
    rw [mem_edgeSet] at hedge
    rw [Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · exact ⟨b, by simp [Finset.mem_filter, mem_neighborFinset, hedge,
        Set.mem_coe, List.mem_toFinset, hmem], rfl⟩
    · refine ⟨a, ?_, Sym2.eq_swap⟩
      simp only [Finset.mem_filter, mem_neighborFinset, Set.mem_coe, List.mem_toFinset]
      exact ⟨hedge.symm, by rwa [show s(v, a) = s(a, v) from Sym2.eq_swap]⟩

/-- **Circuit Removal Preserves Even Degrees** (PROVED):
    If G has all even degrees and we remove the edges of a trail-circuit,
    the remaining graph still has all even degrees.

    This is the key invariant for Hierholzer's algorithm. A circuit
    contributes an even number of edges at each vertex it passes through
    (entering + leaving), so removing it preserves parity.

    **Proof**: Combines three facts:
    1. degree(G, v) = degree(G \ E, v) + |deleted neighbors of v|
    2. |deleted neighbors of v| = countP(v ∈ ·, trail edges)  [bijection]
    3. countP is even for a closed trail  [Mathlib: even_countP_edges_iff]
    Since even = result + even, the result is even. -/
theorem even_degree_after_circuit_removal
    (heven : ∀ v : V, Even (G.degree v))
    {u : V} (p : G.Walk u u) (hp : p.IsTrail) :
    ∀ v : V, Even ((G.deleteEdges (p.edges.toFinset : Set (Sym2 V))).degree v) := by
  intro v
  have hsplit := degree_eq_deleteEdges_add G v (p.edges.toFinset : Set (Sym2 V))
  have hdel := deleted_neighbors_eq_countP G p hp v
  have heven_trail := closed_trail_even_countP G p hp v
  have heven_v := heven v
  rw [hdel] at hsplit
  obtain ⟨k, hk⟩ := heven_v
  obtain ⟨m, hm⟩ := heven_trail
  exact ⟨k - m, by omega⟩

end CycleSplicing

/-
## Part 4: Concrete Example - Triangle Graph K₃

Demonstrates the theory on the simplest graph with an Eulerian circuit:
the complete graph on 3 vertices.
-/

section TriangleExample

/-- Vertices of the triangle graph -/
inductive TriVerts : Type
  | A | B | C
  deriving DecidableEq, Repr

instance : Fintype TriVerts where
  elems := {TriVerts.A, TriVerts.B, TriVerts.C}
  complete := by intro x; cases x <;> simp

open TriVerts

/-- Adjacency for K₃: every pair of distinct vertices is adjacent -/
def triangleAdj : TriVerts → TriVerts → Prop
  | A, B => True | B, A => True
  | B, C => True | C, B => True
  | A, C => True | C, A => True
  | _, _ => False

instance triangleAdjDec : DecidableRel triangleAdj := fun a b => by
  cases a <;> cases b <;> simp [triangleAdj] <;> exact inferInstance

/-- K₃ as a SimpleGraph -/
@[simps]
def triangle : SimpleGraph TriVerts where
  Adj v w := triangleAdj v w
  symm := by intro a b h; cases a <;> cases b <;> simp_all [triangleAdj]
  loopless := by intro a h; cases a <;> simp_all [triangleAdj]

instance : DecidableRel triangle.Adj := triangleAdjDec

/-- Every vertex of K₃ has degree 2 -/
theorem triangle_degree (v : TriVerts) : triangle.degree v = 2 := by
  cases v <;> native_decide

/-- Every vertex of K₃ has even degree -/
theorem triangle_all_even (v : TriVerts) : Even (triangle.degree v) :=
  ⟨1, by rw [triangle_degree]⟩

/-- An explicit Eulerian circuit: A → B → C → A -/
def triangleCircuit : triangle.Walk A A :=
  Walk.cons (show triangle.Adj A B from trivial)
    (Walk.cons (show triangle.Adj B C from trivial)
      (Walk.cons (show triangle.Adj C A from trivial)
        Walk.nil))

/-- The circuit has 3 edges -/
theorem triangleCircuit_length : triangleCircuit.edges.length = 3 := by
  native_decide

/-- The circuit visits all vertices -/
theorem triangleCircuit_visits_all (v : TriVerts) : v ∈ triangleCircuit.support := by
  cases v <;> native_decide

/-- The circuit traverses every edge exactly once. -/
theorem triangleCircuit_isEulerian : triangleCircuit.IsEulerian := by
  intro e he
  revert he
  refine Sym2.ind (fun a b => ?_) e
  intro he
  rw [mem_edgeSet] at he
  cases a <;> cases b <;> simp_all [triangleAdj, triangleCircuit, Walk.edges]

end TriangleExample

/-
## Part 5: Full Characterization Theorems
-/

section Characterization

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Hierholzer's Algorithm Specification**:
    A connected graph with all even degrees and at least one edge
    admits an Eulerian circuit of positive length. -/
theorem hierholzer_spec
    (hconn : G.Connected)
    (heven : ∀ v : V, Even (G.degree v))
    (hne : G.edgeFinset.Nonempty) :
    ∃ v : V, ∃ p : G.Walk v v, p.IsEulerian ∧ 0 < p.edges.length := by
  obtain ⟨v, p, hp⟩ := euler_circuit_exists G hconn heven
  exact ⟨v, p, hp, eulerian_pos_edges G p hp hne⟩

end Characterization

/-
## Summary

### Proved Theorems (10+)
1. `eulerian_edges_toFinset_eq` - Eulerian walk edges = graph edges (as finsets)
2. `eulerian_edges_length` - Eulerian walk edge count = graph edge count
3. `eulerian_pos_edges` - Eulerian circuits have positive edge count
4. `no_eulerian_of_four_odd` - ≥4 odd vertices → no Eulerian path
5. `euler_circuit_all_even` - Eulerian circuit → all even degrees
6. `triangle_degree` / `triangle_all_even` - K₃ has even degrees
7. `triangleCircuit_length` / `triangleCircuit_visits_all` - K₃ circuit properties
8. `triangleCircuit_isEulerian` - K₃ circuit is Eulerian (via Sym2.ind + case analysis)
9. `hierholzer_spec` - Hierholzer algorithm specification (from axiom)
10. `even_degree_after_circuit_removal` - Circuit removal preserves even parity (**PROVED**)
    - `closed_trail_even_countP` - Closed trail incidence is even (from Mathlib)
    - `degree_eq_deleteEdges_add` - Degree decomposition for deleted edges
    - `deleted_neighbors_eq_countP` - Bijection between deleted neighbors and trail incidence

### Axioms (2, reduced from 3)
1. `euler_circuit_exists` - Connected + all even → Eulerian circuit exists
2. `euler_trail_exists` - Connected + exactly 2 odd → Eulerian trail exists

### Sorries (0)

### Progress
- Converted `even_degree_after_circuit_removal` from axiom to theorem
- Reduced axiom count from 3 to 2
- Key Hierholzer invariant is now formally proved

### Mathlib Gap
Mathlib's SimpleGraph.Trails has a TODO: "Prove that there exists an Eulerian
trail when the conclusion to `card_odd_degree` holds." Our `euler_circuit_exists`
and `euler_trail_exists` axioms formally state this missing result.
The `even_degree_after_circuit_removal` theorem (now proved!) captures the
key invariant needed in the inductive proof via Hierholzer's algorithm.
-/

end HierholzerAlgorithm
