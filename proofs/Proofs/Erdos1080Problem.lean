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
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.ConditionallyCompleteLattice.Basic

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
      exact hiff'.mpr huy
    exact ⟨huy, hvx⟩

/--
A graph is bipartite if it admits some bipartition.
-/
def IsBipartite {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ X Y : Set V, IsBipartition G X Y

/--
In a bipartition, no vertex in X is adjacent to another vertex in X.
-/
theorem bipartition_no_edge_within_X {V : Type*} {G : SimpleGraph V} {X Y : Set V}
    (h : IsBipartition G X Y) {u v : V} (hu : u ∈ X) (hv : v ∈ X) :
    ¬G.Adj u v := by
  intro hadj
  -- h.2.2 hadj : u ∈ X ↔ v ∈ Y, so hu gives v ∈ Y
  have hvy : v ∈ Y := (h.2.2 hadj).mp hu
  -- But v ∈ X and X ∩ Y = ∅, contradiction
  exact Set.disjoint_left.mp h.1 hv hvy

/--
In a bipartition, no vertex in Y is adjacent to another vertex in Y.
-/
theorem bipartition_no_edge_within_Y {V : Type*} {G : SimpleGraph V} {X Y : Set V}
    (h : IsBipartition G X Y) {u v : V} (hu : u ∈ Y) (hv : v ∈ Y) :
    ¬G.Adj u v := by
  intro hadj
  -- h.2.2 hadj : u ∈ X ↔ v ∈ Y, so hv (backward) gives u ∈ X
  have hux : u ∈ X := (h.2.2 hadj).mpr hv
  -- But u ∈ Y and X ∩ Y = ∅, contradiction
  exact Set.disjoint_left.mp h.1 hux hu

/--
In a bipartition, membership in the left part is the negation of membership
in the right part (X and Y are literal complements).
-/
theorem mem_left_iff_not_right {V : Type*} {G : SimpleGraph V} {X Y : Set V}
    (h : IsBipartition G X Y) (z : V) : z ∈ X ↔ z ∉ Y := by
  constructor
  · intro hz hzy
    exact Set.disjoint_left.mp h.1 hz hzy
  · intro hz
    have hcover : z ∈ X ∪ Y := by rw [h.2.1]; exact Set.mem_univ z
    rcases hcover with h' | h'
    · exact h'
    · exact absurd h' hz

/--
In a bipartition, membership in the right part is the negation of membership
in the left part.
-/
theorem mem_right_iff_not_left {V : Type*} {G : SimpleGraph V} {X Y : Set V}
    (h : IsBipartition G X Y) (z : V) : z ∈ Y ↔ z ∉ X := by
  have hz := mem_left_iff_not_right h z
  constructor
  · intro hzy hzx
    exact (hz.mp hzx) hzy
  · intro hzx
    by_contra hzy
    exact hzx (hz.mpr hzy)

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

This is denoted f(n,m) in the literature. Defined as `sSup` of achievable
edge counts; for `ℕ`, `sSup` returns 0 for empty sets. Properties are
established by axioms below.
-/
noncomputable def maxC4C6FreeEdges (n m : ℕ) : ℕ :=
  sSup {e : ℕ | ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (X Y : Set V),
    IsBipartition G X Y ∧ X.ncard = n ∧ Y.ncard = m ∧ C4C6Free G ∧ G.edgeSet.ncard = e}

/-
f(n,m) is achieved by some bipartite graph.
-/
/-
## Part IV: De Caen-Székely Bounds (1992)

The key result that disproves Erdős's conjecture.
-/

/-
**De Caen-Székely Upper Bound:**
f(n, ⌊n^(2/3)⌋) ≪ n^(10/9)

More precisely: f(n,m) ≪ (nm)^(2/3) for n^(1/2) ≤ m ≤ n.
-/
/-
**De Caen-Székely Lower Bound:**
f(n, ⌊n^(2/3)⌋) ≫ n^(58/57 + o(1))

This shows that f(n, ⌊n^(2/3)⌋) grows faster than cn for any constant c.
-/
/-
**General Upper Bound:**
For n^(1/2) ≤ m ≤ n: f(n,m) ≪ (nm)^(2/3).
Also proved by Faudree and Simonovits.
-/
/-
## Part V: Lazebnik-Ustimenko-Woldar Improvement (1994)
-/

/-
**Lazebnik-Ustimenko-Woldar Lower Bound (1994):**
f(n, ⌊n^(2/3)⌋) ≫ n^(16/15 + o(1))

This improves De Caen-Székely's lower bound. The constant c is uniform
(independent of n), which is essential for the disproof argument.
-/
/-
## Part V.b: Lazebnik-Ustimenko-Woldar Axiom
-/

/--
**Lazebnik-Ustimenko-Woldar (1994), superlinear formulation:**
For any constant c > 0, sufficiently large bipartite graphs with ⌊N^(2/3)⌋
vertices in one part can be C_4,C_6-free while having ≥ c·N edges.

This follows from the LUW lower bound f(n, ⌊n^(2/3)⌋) ≥ c₀·n^(16/15):
since 16/15 > 1, the edge count grows superlinearly, eventually
exceeding any linear threshold c·N.

We use Fin N as the vertex type to avoid universe issues. -/
axiom luw_superlinear :
  ∀ (c : ℝ), 0 < c → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∃ (G : SimpleGraph (Fin N)) (X Y : Set (Fin N)),
      IsBipartition G X Y ∧
      X.ncard = ⌊(N : ℝ) ^ (2/3 : ℝ)⌋₊ ∧
      C4C6Free G ∧
      (G.edgeSet.ncard : ℝ) ≥ c * N

/-
## Part VI: Disproof of Erdős's Conjecture
-/

/--
**Key Observation:**
Since f(n, ⌊n^(2/3)⌋) ≥ c · n^(16/15) for some c > 0, and 16/15 > 1,
there cannot exist a constant c > 0 such that cn edges guarantee a C_6.

If such c existed, then any C_4,C_6-free graph would have < cn edges,
giving f(n, ⌊n^(2/3)⌋) < cn, contradicting the lower bound.

Proof: from luw_superlinear, for the given c, take a large enough
C_4,C_6-free bipartite graph with ≥ c·N edges. The conjecture says
this graph has a C_6, contradicting C_6-freeness.
-/
theorem erdos_conjecture_false :
    ¬∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) (X Y : Set V),
      IsBipartition G X Y →
      X.ncard = ⌊(Fintype.card V : ℝ) ^ (2/3 : ℝ)⌋₊ →
      G.edgeSet.ncard ≥ c * Fintype.card V →
      HasCycleOfLength G 6 := by
  intro ⟨c, hc, hconj⟩
  -- LUW gives C4C6-free graphs exceeding any linear edge threshold
  obtain ⟨N₀, hLUW⟩ := luw_superlinear c hc
  -- Use N = max N₀ 1 to ensure Fin N is nonempty
  set N := max N₀ 1
  obtain ⟨G, X, Y, hBip, hCardX, hC4C6, hEdges⟩ := hLUW N (le_max_left _ _)
  haveI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  -- Apply the conjecture to get C_6
  have h := hconj (Fin N) G X Y hBip
  simp only [Fintype.card_fin] at h
  -- C4C6Free contradicts HasCycleOfLength G 6
  exact hC4C6.2 (h hCardX hEdges)

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
    ¬∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) (X Y : Set V),
      IsBipartition G X Y → X.ncard = ⌊(Fintype.card V : ℝ) ^ (2/3 : ℝ)⌋₊ →
      G.edgeSet.ncard ≥ c * Fintype.card V →
        HasCycleOfLength G 6 :=
  erdos_conjecture_false

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

/-
**Kővári-Sós-Turán Theorem:**
The maximum number of edges in a bipartite graph with parts of size n
and m that contains no K_{s,t} is at most
  (1/2) · (t-1)^(1/s) · m · n^(1-1/s) + (s-1)n/2.
-/
/--
A `K_{2,2}` in a bipartite graph — two distinct `X`-vertices `a₁, a₂` each
adjacent to two distinct `Y`-vertices `b₁, b₂` — yields a `4`-cycle
`a₁-b₁-a₂-b₂-a₁`.  Assembling the explicit cycle and checking it really is one
(its four vertices are distinct because the two sides of a bipartition are
disjoint) is the substantive content.
-/
theorem hasCycleOfLength_four_of_K22 {V : Type*} {G : SimpleGraph V} {X Y : Set V}
    (h : IsBipartition G X Y)
    {a₁ a₂ b₁ b₂ : V} (ha₁ : a₁ ∈ X) (ha₂ : a₂ ∈ X) (hb₁ : b₁ ∈ Y) (hb₂ : b₂ ∈ Y)
    (hane : a₁ ≠ a₂) (hbne : b₁ ≠ b₂)
    (e11 : G.Adj a₁ b₁) (e12 : G.Adj a₁ b₂) (e21 : G.Adj a₂ b₁) (e22 : G.Adj a₂ b₂) :
    HasCycleOfLength G 4 := by
  -- Cross disequalities: an `X`-vertex and a `Y`-vertex are never equal.
  have ha₁Y : a₁ ∉ Y := (mem_left_iff_not_right h a₁).mp ha₁
  have ha₂Y : a₂ ∉ Y := (mem_left_iff_not_right h a₂).mp ha₂
  have hab11 : a₁ ≠ b₁ := fun heq => ha₁Y (heq ▸ hb₁)
  have hab12 : a₁ ≠ b₂ := fun heq => ha₁Y (heq ▸ hb₂)
  have hab21 : a₂ ≠ b₁ := fun heq => ha₂Y (heq ▸ hb₁)
  have hab22 : a₂ ≠ b₂ := fun heq => ha₂Y (heq ▸ hb₂)
  -- The path `b₁ → a₂ → b₂ → a₁`, built bottom-up so each extension is a path.
  have hp3 : (Walk.cons e12.symm Walk.nil : G.Walk b₂ a₁).IsPath :=
    Walk.IsPath.nil.cons (by
      simp only [Walk.support_nil, List.mem_singleton]; exact hab12.symm)
  have hp2 : (Walk.cons e22 (Walk.cons e12.symm Walk.nil) : G.Walk a₂ a₁).IsPath :=
    hp3.cons (by
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false]
      push_neg; exact ⟨hab22, hane.symm⟩)
  have hp1 : (Walk.cons e21.symm (Walk.cons e22 (Walk.cons e12.symm Walk.nil)) :
      G.Walk b₁ a₁).IsPath :=
    hp2.cons (by
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false]
      push_neg; exact ⟨hab21.symm, hbne, hab11.symm⟩)
  -- Consing the edge `a₁ → b₁` closes the path into a cycle, provided that edge
  -- is not already used.
  refine ⟨a₁, Walk.cons e11 (Walk.cons e21.symm (Walk.cons e22 (Walk.cons e12.symm
    Walk.nil))), ?_, by simp [Walk.length_cons]⟩
  rw [Walk.cons_isCycle_iff]
  refine ⟨hp1, ?_⟩
  have hEdge : ∀ {c d : V}, ¬(a₁ = c ∧ b₁ = d) → ¬(a₁ = d ∧ b₁ = c) →
      s(a₁, b₁) ≠ s(c, d) := by
    intro c d h1 h2 heq
    rw [Sym2.eq_iff] at heq
    rcases heq with hh | hh
    · exact h1 hh
    · exact h2 hh
  simp only [Walk.edges_cons, Walk.edges_nil, List.mem_cons,
    List.not_mem_nil, or_false]
  push_neg
  exact ⟨hEdge (fun hh => hab11 hh.1) (fun hh => hane hh.1),
         hEdge (fun hh => hane hh.1) (fun hh => hab12 hh.1),
         hEdge (fun hh => hab12 hh.1) (fun hh => hbne hh.2)⟩

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
  constructor
  · -- `C₄`-free ⇒ no `K_{2,2}`: a `K_{2,2}` would produce a `4`-cycle.
    intro hC4 a₁ a₂ b₁ b₂ ha₁ ha₂ hane hb₁ hb₂ hbne
    rintro ⟨e11, e12, e21, e22⟩
    exact hC4 (hasCycleOfLength_four_of_K22 h ha₁ ha₂ hb₁ hb₂ hane hbne e11 e12 e21 e22)
  · -- no `K_{2,2}` ⇒ `C₄`-free: a `4`-cycle would produce a `K_{2,2}`.
    intro hforbid ⟨v, w, hcyc, hlen⟩
    -- A closed walk of length `4` decomposes as four consecutive edges.
    cases w with
    | nil => simp at hlen
    | @cons _ x1 _ g1 w1 =>
    cases w1 with
    | nil => simp at hlen
    | @cons _ x2 _ g2 w2 =>
    cases w2 with
    | nil => simp at hlen
    | @cons _ x3 _ g3 w3 =>
    cases w3 with
    | nil => simp at hlen
    | @cons _ x4 _ g4 w4 =>
    cases w4 with
    | cons g5 w5 => simp only [Walk.length_cons] at hlen; omega
    | nil =>
      -- `w = v → x1 → x2 → x3 → v`; the four inner vertices are distinct.
      have htail := (Walk.isCycle_def _).mp hcyc |>.2.2
      simp only [Walk.support_cons, Walk.support_nil, List.tail_cons, List.nodup_cons,
        List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false,
        and_true] at htail
      push_neg at htail
      obtain ⟨⟨_h12, h13, _h1v⟩, ⟨_h23, h2v⟩, _h3v⟩ := htail
      have hv : v ∈ X ∪ Y := by rw [h.2.1]; exact Set.mem_univ v
      rcases hv with hvX | hvY
      · -- `v ∈ X`, so the walk alternates `X, Y, X, Y`.
        have hx1 : x1 ∈ Y := (h.2.2 g1).mp hvX
        have hx1nX : x1 ∉ X := (mem_right_iff_not_left h x1).mp hx1
        have hx2 : x2 ∈ X :=
          (mem_left_iff_not_right h x2).mpr (fun hx2Y => hx1nX ((h.2.2 g2).mpr hx2Y))
        have hx3 : x3 ∈ Y := (h.2.2 g3).mp hx2
        exact hforbid v x2 x1 x3 hvX hx2 h2v.symm hx1 hx3 h13 ⟨g1, g4.symm, g2.symm, g3⟩
      · -- `v ∈ Y`, so the walk alternates `Y, X, Y, X`.
        have hvnX : v ∉ X := (mem_right_iff_not_left h v).mp hvY
        have hx1 : x1 ∈ X :=
          (mem_left_iff_not_right h x1).mpr (fun hx1Y => hvnX ((h.2.2 g1).mpr hx1Y))
        have hx2 : x2 ∈ Y := (h.2.2 g2).mp hx1
        have hx2nX : x2 ∉ X := (mem_right_iff_not_left h x2).mp hx2
        have hx3 : x3 ∈ X :=
          (mem_left_iff_not_right h x3).mpr (fun hx3Y => hx2nX ((h.2.2 g3).mpr hx3Y))
        exact hforbid x1 x3 v x2 hx1 hx3 h13 hvY hx2 h2v.symm ⟨g1.symm, g2, g4, g3.symm⟩

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
