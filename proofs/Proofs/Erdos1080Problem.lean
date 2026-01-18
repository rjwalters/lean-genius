/-
Erdős Problem #1080: Six-Cycles in Sparse Bipartite Graphs

Source: https://erdosproblems.com/1080
Status: DISPROVED (De Caen-Székely, 1992)

Statement:
Let G be a bipartite graph on n vertices such that one part has ⌊n^(2/3)⌋
vertices. Is there a constant c > 0 such that if G has at least cn edges
then G must contain a C_6 (six-cycle)?

Answer: NO

De Caen and Székely (1992) showed the answer is no. They proved:
  n^(10/9) ≫ f(n, ⌊n^(2/3)⌋) ≫ n^(58/57 + o(1))
where f(n,m) is the maximum number of edges in a bipartite graph between
n and m vertices containing no C_4 or C_6.

A positive answer would have implied f(n, ⌊n^(2/3)⌋) ≪ n.

Lazebnik, Ustimenko, and Woldar (1994) improved the lower bound to:
  f(n, ⌊n^(2/3)⌋) ≫ n^(16/15 + o(1))

Note: Erdős observed that it is easy to see that such a graph must
contain a C_8 (eight-cycle).

References:
- Erdős [Er75]: Original problem, C_8 observation
- De Caen & Székely [DeSz92]: Disproof and f(n,m) bounds
- Lazebnik, Ustimenko & Woldar [LUW94]: Improved lower bound
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card

open SimpleGraph Set

namespace Erdos1080

/-
## Part I: Bipartite Graphs and Bipartitions
-/

/--
**IsBipartition G X Y:**
The vertex set of G is partitioned into disjoint sets X and Y such that
all edges go between X and Y.

A bipartite graph is one that admits such a bipartition.
-/
def IsBipartition {V : Type*} (G : SimpleGraph V) (X Y : Set V) : Prop :=
  Disjoint X Y ∧ X ∪ Y = Set.univ ∧ ∀ ⦃u v⦄, G.Adj u v → (u ∈ X ↔ v ∈ Y)

/--
If (X, Y) is a bipartition, then edges only go between X and Y.
-/
theorem bipartition_edges_between {V : Type*} (G : SimpleGraph V) (X Y : Set V)
    (h : IsBipartition G X Y) : ∀ ⦃u v⦄, G.Adj u v → (u ∈ X ∧ v ∈ Y) ∨ (u ∈ Y ∧ v ∈ X) := by
  intro u v hadj
  have hiff := h.2.2 hadj
  have hcover : u ∈ X ∪ Y := by rw [h.2.1]; trivial
  cases hcover with
  | inl hux =>
    left
    exact ⟨hux, hiff.mp hux⟩
  | inr huy =>
    right
    have hvx : v ∈ X := by
      have := G.symm hadj
      have hiff' := h.2.2 this
      exact hiff'.mp huy
    exact ⟨huy, hvx⟩

/--
A graph is bipartite if it admits some bipartition.
-/
def IsBipartite {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ X Y : Set V, IsBipartition G X Y

/-
## Part II: Cycles in Graphs
-/

/--
**HasCycleOfLength G k:**
The graph G contains a cycle of length k.
-/
def HasCycleOfLength {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (v : V) (walk : G.Walk v v), walk.IsCycle ∧ walk.length = k

/--
**C4Free G:**
The graph G contains no 4-cycle.
-/
def C4Free {V : Type*} (G : SimpleGraph V) : Prop := ¬HasCycleOfLength G 4

/--
**C6Free G:**
The graph G contains no 6-cycle.
-/
def C6Free {V : Type*} (G : SimpleGraph V) : Prop := ¬HasCycleOfLength G 6

/--
**C4C6Free G:**
The graph G contains no 4-cycle and no 6-cycle.
-/
def C4C6Free {V : Type*} (G : SimpleGraph V) : Prop := C4Free G ∧ C6Free G

/-
## Part III: The Extremal Function f(n,m)
-/

/--
**maxC4C6FreeEdges n m:**
The maximum number of edges in a bipartite graph with parts of size n and m
that contains no C_4 or C_6.

This is denoted f(n,m) in the literature.
-/
def maxC4C6FreeEdges (n m : ℕ) : ℕ :=
  sorry -- Defined as supremum; axiomatized below

/--
f(n,m) is achieved by some bipartite graph.
-/
axiom maxC4C6FreeEdges_achieved (n m : ℕ) (hn : n ≥ 1) (hm : m ≥ 1) :
    ∃ (V : Type) [Fintype V] (G : SimpleGraph V) (X Y : Set V),
      IsBipartition G X Y ∧
      X.ncard = n ∧
      Y.ncard = m ∧
      C4C6Free G ∧
      G.edgeSet.ncard = maxC4C6FreeEdges n m

/-
## Part IV: De Caen-Székely Bounds (1992)

The key result that disproves Erdős's conjecture.
-/

/--
**De Caen-Székely Upper Bound:**
f(n, ⌊n^(2/3)⌋) ≪ n^(10/9)

More precisely: f(n,m) ≪ (nm)^(2/3) for n^(1/2) ≤ m ≤ n.
-/
axiom deCaen_szekely_upper_bound (n : ℕ) (hn : n ≥ 2) :
    ∃ C : ℝ, C > 0 ∧
      (maxC4C6FreeEdges n ⌊(n : ℝ) ^ (2/3 : ℝ)⌋₊ : ℝ) ≤ C * (n : ℝ) ^ (10/9 : ℝ)

/--
**De Caen-Székely Lower Bound:**
f(n, ⌊n^(2/3)⌋) ≫ n^(58/57 + o(1))

This shows that f(n, ⌊n^(2/3)⌋) grows faster than cn for any constant c.
-/
axiom deCaen_szekely_lower_bound (n : ℕ) (hn : n ≥ 2) :
    ∃ c : ℝ, c > 0 ∧
      (maxC4C6FreeEdges n ⌊(n : ℝ) ^ (2/3 : ℝ)⌋₊ : ℝ) ≥ c * (n : ℝ) ^ (58/57 : ℝ)

/--
**General Upper Bound:**
For n^(1/2) ≤ m ≤ n: f(n,m) ≪ (nm)^(2/3).
Also proved by Faudree and Simonovits.
-/
axiom faudree_simonovits_bound (n m : ℕ) (hn : n ≥ 1) (hm : m ≥ 1)
    (hlo : (n : ℝ) ^ (1/2 : ℝ) ≤ m) (hhi : (m : ℝ) ≤ n) :
    ∃ C : ℝ, C > 0 ∧
      (maxC4C6FreeEdges n m : ℝ) ≤ C * ((n : ℝ) * m) ^ (2/3 : ℝ)

/-
## Part V: Lazebnik-Ustimenko-Woldar Improvement (1994)
-/

/--
**Lazebnik-Ustimenko-Woldar Lower Bound (1994):**
f(n, ⌊n^(2/3)⌋) ≫ n^(16/15 + o(1))

This improves De Caen-Székely's lower bound.
-/
axiom lazebnik_ustimenko_woldar_bound (n : ℕ) (hn : n ≥ 2) :
    ∃ c : ℝ, c > 0 ∧
      (maxC4C6FreeEdges n ⌊(n : ℝ) ^ (2/3 : ℝ)⌋₊ : ℝ) ≥ c * (n : ℝ) ^ (16/15 : ℝ)

/-
## Part VI: Disproof of Erdős's Conjecture
-/

/--
**Key Observation:**
Since f(n, ⌊n^(2/3)⌋) ≥ c · n^(16/15) for some c > 0, and 16/15 > 1,
there cannot exist a constant c > 0 such that cn edges guarantee a C_6.

If such c existed, then any C_4,C_6-free graph would have < cn edges,
giving f(n, ⌊n^(2/3)⌋) < cn, contradicting the lower bound.
-/
theorem erdos_conjecture_false :
    ¬∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) (X Y : Set V),
      IsBipartition G X Y →
      X.ncard = ⌊(Fintype.card V : ℝ) ^ (2/3 : ℝ)⌋₊ →
      G.edgeSet.ncard ≥ c * Fintype.card V →
      HasCycleOfLength G 6 := by
  intro ⟨c, hc, hconj⟩
  -- The conjecture would imply f(n, ⌊n^(2/3)⌋) < cn for all large n
  -- But Lazebnik-Ustimenko-Woldar shows f(n, ⌊n^(2/3)⌋) ≥ c' · n^(16/15)
  -- For large n, c' · n^(16/15) > cn, contradiction
  sorry

/--
**Erdős Problem #1080: DISPROVED**

The answer to Erdős's question is NO.

Let G be a bipartite graph on n vertices with one part having ⌊n^(2/3)⌋ vertices.
There is NO constant c > 0 such that having at least cn edges guarantees
a 6-cycle.

This is because C_4,C_6-free bipartite graphs can have superlinearly
many edges (specifically, Ω(n^(16/15)) edges).
-/
theorem erdos_1080 :
    answer(false) ↔
    ∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) (X Y : Set V),
      IsBipartition G X Y → X.ncard = ⌊(Fintype.card V : ℝ) ^ (2/3 : ℝ)⌋₊ →
      G.edgeSet.ncard ≥ c * Fintype.card V →
        HasCycleOfLength G 6 := by
  -- answer(false) means the answer to the question is NO
  -- The question asks if such c exists; the answer is NO
  sorry

/-
## Part VII: The C_8 Observation
-/

/--
**Erdős's Observation:**
Any bipartite graph with ⌊n^(2/3)⌋ vertices in one part and cn edges
must contain a C_8 (eight-cycle).

This is "easy to see" according to Erdős [Er75].
-/
axiom erdos_c8_observation :
    ∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) (X Y : Set V),
      IsBipartition G X Y → X.ncard = ⌊(Fintype.card V : ℝ) ^ (2/3 : ℝ)⌋₊ →
      G.edgeSet.ncard ≥ c * Fintype.card V →
        HasCycleOfLength G 8

/-
## Part VIII: Related Extremal Results
-/

/--
**Kővári-Sós-Turán Theorem:**
The maximum number of edges in a bipartite graph with parts of size n
and m that contains no K_{s,t} is at most
  (1/2) · (t-1)^(1/s) · m · n^(1-1/s) + (s-1)n/2.
-/
axiom kovari_sos_turan (n m s t : ℕ) (hs : s ≥ 1) (ht : t ≥ s) :
    ∃ ex : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (X Y : Set V),
      IsBipartition G X Y → X.ncard = n → Y.ncard = m →
      (∀ (A : Finset V) (B : Finset V),
        A.card = s → B.card = t →
        (∀ a ∈ A, a ∈ X) → (∀ b ∈ B, b ∈ Y) →
        ∃ a ∈ A, ∃ b ∈ B, ¬G.Adj a b) →
      G.edgeSet.ncard ≤ ex

/--
A bipartite graph with no C_4 is the same as a graph with no K_{2,2}.
-/
theorem c4_free_iff_no_K22 {V : Type*} (G : SimpleGraph V) (X Y : Set V)
    (h : IsBipartition G X Y) :
    C4Free G ↔
    ∀ (a₁ a₂ : V) (b₁ b₂ : V),
      a₁ ∈ X → a₂ ∈ X → a₁ ≠ a₂ →
      b₁ ∈ Y → b₂ ∈ Y → b₁ ≠ b₂ →
      ¬(G.Adj a₁ b₁ ∧ G.Adj a₁ b₂ ∧ G.Adj a₂ b₁ ∧ G.Adj a₂ b₂) := by
  sorry

/-
## Part IX: Summary
-/

/--
**Summary of Erdős Problem #1080:**

1. The question asks if cn edges guarantee a C_6 in bipartite graphs
   with ⌊n^(2/3)⌋ vertices in one part.

2. The answer is NO (De Caen-Székely, 1992).

3. The extremal function f(n, ⌊n^(2/3)⌋) satisfies:
   - Lower bound: Ω(n^(16/15)) (Lazebnik-Ustimenko-Woldar, 1994)
   - Upper bound: O(n^(10/9)) (De Caen-Székely, 1992)

4. In contrast, cn edges DO guarantee a C_8 (Erdős's observation).
-/
theorem erdos_1080_summary :
    (¬∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) (X Y : Set V),
      IsBipartition G X Y → X.ncard = ⌊(Fintype.card V : ℝ) ^ (2/3 : ℝ)⌋₊ →
      G.edgeSet.ncard ≥ c * Fintype.card V → HasCycleOfLength G 6) ∧
    (∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) (X Y : Set V),
      IsBipartition G X Y → X.ncard = ⌊(Fintype.card V : ℝ) ^ (2/3 : ℝ)⌋₊ →
      G.edgeSet.ncard ≥ c * Fintype.card V → HasCycleOfLength G 8) :=
  ⟨erdos_conjecture_false, erdos_c8_observation⟩

end Erdos1080
