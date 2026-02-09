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

Authors: lean-genius research (researcher-2)
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
-/

section CycleSplicing

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Circuit Removal Preserves Even Degrees**:
    If G has all even degrees and we remove the edges of a trail-circuit,
    the remaining graph still has all even degrees.

    This is the key invariant for Hierholzer's algorithm. A circuit
    contributes degree 2 at each vertex it passes through (entering + leaving),
    so removing it preserves parity. -/
axiom even_degree_after_circuit_removal
    (heven : ∀ v : V, Even (G.degree v))
    {u : V} (p : G.Walk u u) (hp : p.IsTrail) :
    ∀ v : V, Even ((G.deleteEdges (p.edges.toFinset : Set (Sym2 V))).degree v)

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
  -- We verify by exhaustive computation on the 3 edges of K₃
  simp only [triangleCircuit, Walk.edges]
  simp only [triangle, edgeSet] at he
  -- Each edge of K₃ appears exactly once in [s(A,B), s(B,C), s(C,A)]
  sorry

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

### Proved Theorems (8)
1. `eulerian_edges_toFinset_eq` - Eulerian walk edges = graph edges (as finsets)
2. `eulerian_edges_length` - Eulerian walk edge count = graph edge count
3. `eulerian_pos_edges` - Eulerian circuits have positive edge count
4. `no_eulerian_of_four_odd` - ≥4 odd vertices → no Eulerian path
5. `euler_circuit_all_even` - Eulerian circuit → all even degrees
6. `triangle_degree` / `triangle_all_even` - K₃ has even degrees
7. `triangleCircuit_length` / `triangleCircuit_visits_all` - K₃ circuit properties
8. `hierholzer_spec` - Hierholzer algorithm specification (from axiom)

### Axioms (3)
1. `euler_circuit_exists` - Connected + all even → Eulerian circuit exists
2. `euler_trail_exists` - Connected + exactly 2 odd → Eulerian trail exists
3. `even_degree_after_circuit_removal` - Circuit removal preserves even parity

### Sorries (1)
1. `triangleCircuit_isEulerian` - K₃ circuit is Eulerian (decidable but needs instance)

### Mathlib Gap
Mathlib's SimpleGraph.Trails has a TODO: "Prove that there exists an Eulerian
trail when the conclusion to `card_odd_degree` holds." Our `euler_circuit_exists`
and `euler_trail_exists` axioms formally state this missing result. The
`even_degree_after_circuit_removal` axiom captures the key invariant that would
be needed in the inductive proof via Hierholzer's algorithm.
-/

end HierholzerAlgorithm
