/-
Copyright (c) 2024-2025 lean-genius contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Set.Card

/-!
# The Friendship Theorem

## What This Proves

The **Friendship Theorem** (Erdős–Rényi–Sós, 1966) states: In any finite simple graph
where every pair of distinct vertices has exactly one common neighbor, there exists
a vertex adjacent to all other vertices (a "universal friend" or "politician").

**Equivalently**: The only graphs satisfying the friendship property are "windmill graphs"
(also called "Dutch windmills" or "friendship graphs") — collections of triangles sharing
a common central vertex.

## Mathematical Statement

Let $G = (V, E)$ be a finite simple graph. The **friendship property** states:
$$\forall u, v \in V, \, u \neq v \implies |\{w : w \sim u \land w \sim v\}| = 1$$

The theorem concludes: $\exists c \in V$ such that $\forall v \in V, \, v \neq c \implies c \sim v$.

## Proof Approach

The classical proof by Erdős, Rényi, and Sós uses spectral graph theory:
1. Study the adjacency matrix $A$ of the graph
2. Show $A^2 = J - I + kA$ for some regularity constant $k$ (or handle irregular case)
3. Analyze eigenvalues to derive a contradiction unless a universal vertex exists
4. The key insight: if no universal vertex exists, all vertices have the same degree,
   leading to specific eigenvalue constraints that force the graph to be regular

Here we provide a formal proof using counting arguments and properties of
friendship graphs.

## Status
- [x] Definition of friendship property
- [x] Definition of windmill graphs
- [x] Statement of main theorem
- [ ] Complete proof (some lemmas use sorry)

## Mathlib Dependencies
- `SimpleGraph` : Undirected graphs without self-loops
- `SimpleGraph.commonNeighbors` : Set of common neighbors
- `Set.ncard` : Cardinality of a set

Historical Note: This theorem was proved by Paul Erdős, Alfréd Rényi, and
Vera T. Sós in 1966 and has become a classic result in combinatorics.
-/

namespace FriendshipTheorem

open SimpleGraph Finset BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-!
## Part 1: The Friendship Property

We define the friendship property: every pair of distinct vertices has
exactly one common neighbor.
-/

/-- A graph satisfies the **friendship property** if every pair of distinct
vertices has exactly one common neighbor. We use `Set.ncard` to count
elements in the set of common neighbors. -/
def IsFriendshipGraph (G : SimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → (G.commonNeighbors u v).ncard = 1

/-- A vertex `c` is **universal** (or a "politician") if it's adjacent to
all other vertices. -/
def IsUniversalVertex (G : SimpleGraph V) (c : V) : Prop :=
  ∀ v : V, v ≠ c → G.Adj c v

/-- The number of common neighbors as a natural number (using Set.ncard). -/
noncomputable def commonNeighborCount (G : SimpleGraph V) (u v : V) : ℕ :=
  (G.commonNeighbors u v).ncard

/-!
## Part 2: Windmill Graphs

The windmill graph $W_n$ consists of $n$ triangles sharing a common vertex.
These are the only friendship graphs.
-/

/-- A windmill graph is defined by having a universal vertex where removing
that vertex leaves a disjoint union of edges (triangles with the center). -/
def IsWindmillGraph (G : SimpleGraph V) : Prop :=
  ∃ c : V, IsUniversalVertex G c ∧
    ∀ u v : V, u ≠ c → v ≠ c → u ≠ v →
      ¬G.Adj u v → G.commonNeighbors u v = {c}

/-!
## Part 3: Key Lemmas

These lemmas establish properties of friendship graphs that lead to the
existence of a universal vertex.
-/

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In a friendship graph with at least 2 vertices, every vertex has
positive degree (is adjacent to at least one other vertex). -/
lemma friendship_positive_degree (hF : IsFriendshipGraph G) (h : Fintype.card V ≥ 2) :
    ∀ v : V, G.degree v > 0 := by
  intro v
  -- Since n ≥ 2, there exists some u ≠ v
  -- By friendship property, v and u have a common neighbor w
  -- So w is adjacent to v, meaning degree v > 0
  sorry

/-- In a friendship graph, the number of vertices is odd. -/
lemma friendship_card_odd (hF : IsFriendshipGraph G) (h : Fintype.card V ≥ 3) :
    Odd (Fintype.card V) := by
  -- The proof uses counting: each vertex has some degree d, and the
  -- friendship property constrains the total structure
  -- In a friendship graph with n vertices, n must be odd
  -- This follows from the windmill structure
  sorry

/-- In a non-trivial friendship graph, there exists a vertex of maximum degree
that is adjacent to all others, or the graph is regular. -/
lemma friendship_has_universal_or_regular (hF : IsFriendshipGraph G)
    (h : Fintype.card V ≥ 3) :
    (∃ c : V, IsUniversalVertex G c) ∨
    (∃ k : ℕ, ∀ v : V, G.degree v = k) := by
  -- Either some vertex has maximum degree n-1 (universal),
  -- or by the friendship property's symmetry, all degrees are equal
  sorry

/-- If a friendship graph is regular (all vertices same degree), and has
no universal vertex, then it must have a very specific structure that
leads to a contradiction for n > 3. -/
lemma friendship_regular_implies_universal (hF : IsFriendshipGraph G)
    (hReg : ∃ k : ℕ, ∀ v : V, G.degree v = k)
    (h : Fintype.card V ≥ 3) :
    ∃ c : V, IsUniversalVertex G c := by
  -- The spectral approach: if G is k-regular with n vertices and satisfies
  -- friendship, then A² = J - I + (k-1)A where A is adjacency matrix.
  -- The eigenvalues must satisfy certain conditions.
  -- For a regular friendship graph, each vertex must be universal.
  sorry

/-!
## Part 4: The Main Theorem

The Friendship Theorem: every friendship graph on 3+ vertices has a universal
vertex (a "politician").
-/

/-- **The Friendship Theorem** (Erdős–Rényi–Sós, 1966)

In any finite simple graph where every pair of distinct vertices has exactly
one common neighbor, there exists a vertex adjacent to all other vertices.

This vertex is called the "politician" — the one who is friends with everyone.
The resulting graph structure must be a windmill: triangles sharing a common vertex.
-/
theorem friendship_theorem (hF : IsFriendshipGraph G) (h : Fintype.card V ≥ 3) :
    ∃ c : V, IsUniversalVertex G c := by
  -- By friendship_has_universal_or_regular, either we're done or G is regular
  rcases friendship_has_universal_or_regular G hF h with ⟨c, hc⟩ | hReg
  · exact ⟨c, hc⟩
  -- If regular, the spectral argument gives us a universal vertex
  exact friendship_regular_implies_universal G hF hReg h

/-- The friendship theorem implies every friendship graph is a windmill. -/
theorem friendship_graph_is_windmill (hF : IsFriendshipGraph G) (h : Fintype.card V ≥ 3) :
    IsWindmillGraph G := by
  obtain ⟨c, hc⟩ := friendship_theorem G hF h
  refine ⟨c, hc, ?_⟩
  -- For non-adjacent pairs among non-central vertices, they share only c
  intro u v hu hv _ hnadj
  -- Since u and v are both adjacent to c, c is a common neighbor
  -- By friendship property, they have exactly one, so it must be c
  ext w
  constructor
  · intro hw
    simp only [Set.mem_singleton_iff]
    -- w is adjacent to both u and v
    -- If w ≠ c, then since u ~ c and w ~ u, and u ~ v is false,
    -- we need to use friendship property carefully
    by_contra hwc
    -- u and w are distinct (since w is a neighbor of u, not equal)
    -- They have exactly one common neighbor by friendship
    -- Both c and v? No, v is not adjacent to u
    sorry
  · intro hw
    simp only [Set.mem_singleton_iff] at hw
    subst hw
    -- c is in commonNeighbors u v means c ~ u and c ~ v
    simp only [commonNeighbors, Set.mem_setOf_eq, mem_neighborSet]
    constructor <;> [exact G.symm (hc u hu); exact G.symm (hc v hv)]

/-!
## Part 5: Examples

### The Windmill Graph W₂ (Two Triangles)

```
      1
     /|\
    / | \
   2--0--3
    \ | /
     \|/
      4
```

Vertex 0 is universal, vertices {1,2} and {3,4} form triangle pairs with 0.
-/

/-- Adjacency relation for the 5-vertex windmill W₂.
Vertex 0 is adjacent to all others; additionally (1,2) and (3,4) are adjacent. -/
def windmill2Adj (u v : Fin 5) : Prop :=
  (u = 0 ∧ v ≠ 0) ∨ (v = 0 ∧ u ≠ 0) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) ∨
  (u = 3 ∧ v = 4) ∨ (u = 4 ∧ v = 3)

instance : DecidableRel windmill2Adj := fun u v => by
  unfold windmill2Adj
  infer_instance

/-- The 5-vertex windmill W₂ with two triangles sharing vertex 0. -/
def windmill2 : SimpleGraph (Fin 5) where
  Adj := windmill2Adj
  symm := by
    intro u v h
    unfold windmill2Adj at *
    tauto
  loopless := by
    intro v h
    unfold windmill2Adj at h
    omega

instance : DecidableRel windmill2.Adj := inferInstanceAs (DecidableRel windmill2Adj)

/-- Vertex 0 is universal in W₂. -/
lemma windmill2_has_universal : IsUniversalVertex windmill2 0 := by
  intro v hv
  unfold windmill2 windmill2Adj
  left
  exact ⟨rfl, hv⟩

/-- W₂ satisfies the friendship property. -/
lemma windmill2_is_friendship : IsFriendshipGraph windmill2 := by
  intro u v huv
  -- Each pair of distinct vertices has exactly one common neighbor
  -- For pairs involving 0: their unique common neighbor depends on which pair
  -- For pairs like (1,2): 0 is their unique common neighbor
  -- For pairs like (1,3): 0 is their unique common neighbor
  sorry

/-!
## Historical Notes

### The 1966 Paper

Erdős, Rényi, and Sós published their proof in "On a problem of graph theory"
in Studia Scientiarum Mathematicarum Hungarica (1966).

### The Name "Friendship Theorem"

The evocative name comes from the sociological interpretation:
- Vertices represent people
- Edges represent mutual friendship
- The condition says: any two people have exactly one mutual friend
- The conclusion: there must be a "politician" who is friends with everyone

### Alternative Proofs

1. **Spectral proof** (original): Uses eigenvalues of the adjacency matrix
2. **Counting proof**: Uses careful degree-counting arguments
3. **Algebraic proof**: Views the condition as a matrix equation

The spectral proof remains the most elegant, showing that the eigenvalue
structure of friendship graphs is highly constrained.

### Connection to Combinatorics

The friendship theorem is related to:
- Strongly regular graphs (friendship graphs are almost regular)
- Finite geometry (certain projective planes)
- Design theory (balanced incomplete block designs)
-/

#check @friendship_theorem
#check @friendship_graph_is_windmill

end FriendshipTheorem
