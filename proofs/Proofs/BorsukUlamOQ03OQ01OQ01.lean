import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-
# Tucker 2D Lemma: Graph-Theoretic Path-Following (OQ-03-OQ-01-OQ-01)

## What This Proves

This file formalizes the combinatorial core of Tucker's lemma in 2D via
graph-theoretic path-following. The key idea: construct a graph from a Tucker
labeling, apply a parity argument to force the existence of a complementary edge.

## The Graph-Theoretic Approach

Given a triangulated disk with antipodal boundary labeling by {±1, ±2}:

1. Construct the Tucker graph (vertices = triangles, edges = shared complementary edges)
2. Analyze vertex degrees (interior = 0 or 2, boundary = possibly 1)
3. Apply parity: odd boundary count forces interior complementary edge

## Extends
- BorsukUlamOQ03OQ01.lean: Tucker 1D and quantitative BU bounds
- BorsukUlamOQ03.lean: Constructive 1D Borsuk-Ulam
-/

namespace TuckerPathFollowing

open Finset

-- ========================================================================
-- Part I: Tucker Labeling Definitions
-- ========================================================================

/-- A Tucker labeling assigns ±1 or ±2 to each vertex. -/
structure TuckerLabeling (V : Type*) [Fintype V] where
  label : V → ℤ
  range : ∀ v, label v = -2 ∨ label v = -1 ∨ label v = 1 ∨ label v = 2

/-- An antipodal Tucker labeling has an involution σ with label(σ(v)) = -label(v). -/
structure AntipodalTuckerLabeling (V : Type*) [Fintype V]
    extends TuckerLabeling V where
  antipodal : V → V
  antipodal_invol : ∀ v, antipodal (antipodal v) = v
  antipodal_label : ∀ v, label (antipodal v) = -(label v)

/-- Two vertices form a complementary pair if their labels sum to zero. -/
def isComplementary [Fintype V] (l : TuckerLabeling V) (v w : V) : Prop :=
  l.label v + l.label w = 0

/-- Complementary is decidable (it's an integer equation). -/
instance [Fintype V] (l : TuckerLabeling V) (v w : V) :
    Decidable (isComplementary l v w) :=
  inferInstanceAs (Decidable (l.label v + l.label w = 0))

/-- Complementary is symmetric. -/
theorem isComplementary_symm [Fintype V] (l : TuckerLabeling V) (v w : V) :
    isComplementary l v w ↔ isComplementary l w v := by
  simp [isComplementary, add_comm]

/-- In an antipodal labeling, v and σ(v) are always complementary. -/
theorem antipodal_complementary [Fintype V] (l : AntipodalTuckerLabeling V) (v : V) :
    isComplementary l.toTuckerLabeling v (l.antipodal v) := by
  simp [isComplementary, l.antipodal_label]

-- ========================================================================
-- Part II: Labels Can Only Form Specific Complementary Pairs
-- ========================================================================

/-- The only complementary pairs from {±1, ±2} are (1,-1) and (2,-2). -/
theorem complementary_pairs [Fintype V] (l : TuckerLabeling V) (v w : V)
    (h : isComplementary l v w) :
    (l.label v = 1 ∧ l.label w = -1) ∨
    (l.label v = -1 ∧ l.label w = 1) ∨
    (l.label v = 2 ∧ l.label w = -2) ∨
    (l.label v = -2 ∧ l.label w = 2) := by
  unfold isComplementary at h
  rcases l.range v with hv | hv | hv | hv <;>
    rcases l.range w with hw | hw | hw | hw <;>
    simp_all (config := { decide := true })

-- ========================================================================
-- Part III: Triangulated Complex
-- ========================================================================

/-- A triangulated 2-complex with vertex set V and triangle set T. -/
structure TriangulatedComplex (V T : Type*) [Fintype V] [Fintype T] where
  /-- The three vertices of each triangle. -/
  vertices : T → Fin 3 → V
  /-- Two triangles are adjacent if they share an edge. -/
  adj : T → T → Prop
  adj_symm : ∀ t₁ t₂, adj t₁ t₂ → adj t₂ t₁
  adj_irrefl : ∀ t, ¬adj t t

/-- A triangle has a complementary edge if two of its three edges are
labeled with opposite values. -/
def hasComplementaryEdge [Fintype V] [Fintype T]
    (K : TriangulatedComplex V T) (l : TuckerLabeling V) (t : T) : Prop :=
  ∃ i j : Fin 3, i ≠ j ∧ isComplementary l (K.vertices t i) (K.vertices t j)

/-- Decidability of hasComplementaryEdge. -/
instance [Fintype V] [Fintype T] [DecidableEq V] [DecidableEq (Fin 3)]
    (K : TriangulatedComplex V T) (l : TuckerLabeling V) (t : T) :
    Decidable (hasComplementaryEdge K l t) :=
  inferInstanceAs (Decidable (∃ i j : Fin 3, i ≠ j ∧ isComplementary l (K.vertices t i) (K.vertices t j)))

-- ========================================================================
-- Part IV: Boundary Classification
-- ========================================================================

/-- Predicate: a triangle is on the boundary of the complex. -/
class HasBoundary (T : Type*) where
  isBoundary : T → Prop
  isBoundary_dec : DecidablePred isBoundary

attribute [instance] HasBoundary.isBoundary_dec

-- ========================================================================
-- Part V: Complementary Degree
-- ========================================================================

/-- The number of complementary edge-pairs in a triangle. Counts unordered
pairs {i,j} with i < j whose vertices have opposite labels.
For Tucker labels from {±1, ±2}, this is at most 2. -/
def complementaryDegree [Fintype V] [Fintype T]
    (K : TriangulatedComplex V T) (l : TuckerLabeling V) (t : T) : ℕ :=
  (Finset.univ.filter (fun p : Fin 3 × Fin 3 =>
    p.1 < p.2 ∧ isComplementary l (K.vertices t p.1) (K.vertices t p.2))).card

/-- Positive complementary degree is equivalent to having a complementary edge. -/
theorem hasComplementaryEdge_iff_complementaryDegree_pos [Fintype V] [Fintype T]
    (K : TriangulatedComplex V T) (l : TuckerLabeling V) (t : T) :
    hasComplementaryEdge K l t ↔ 0 < complementaryDegree K l t := by
  constructor
  · rintro ⟨i, j, hij, hcomp⟩
    rw [complementaryDegree, Finset.card_pos]
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨⟨i, j⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, hcomp⟩⟩
    · exact ⟨⟨j, i⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h,
        (isComplementary_symm l _ _).mp hcomp⟩⟩
  · intro h
    rw [complementaryDegree, Finset.card_pos] at h
    obtain ⟨⟨i, j⟩, hmem⟩ := h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact ⟨i, j, ne_of_lt hmem.1, hmem.2⟩

-- ========================================================================
-- Part VI: The Parity Principle (Core Argument)
-- ========================================================================

/-
**The Parity Argument for Tucker's Lemma** (via handshaking):

1. Construct the Tucker graph G:
   - Vertices = triangles of the complex
   - Edges = pairs of triangles sharing an interior complementary edge

2. By the handshaking lemma (Σ degrees = 2|E|):
   The number of odd-degree vertices in G is even.

3. For interior triangles: G-degree = complementary degree
   (all edges of an interior triangle are interior, hence shared)

4. Partition odd-degree triangles into boundary and interior.
   If the boundary portion has odd cardinality, the interior portion
   must also have odd cardinality (since their sum is even).

5. An interior triangle with odd G-degree has positive complementary
   degree, hence possesses a complementary edge.
-/

/-- **Tucker's Parity Principle**: If the handshaking lemma holds for the
Tucker graph and the boundary contributes an odd number of odd-degree
triangles, then some interior triangle has a complementary edge.

The Tucker graph degree function `tuckerDeg` abstracts the graph where
vertices = triangles and edges = shared interior complementary edges.
The three hypotheses encode:
- `h_interior_deg`: interior Tucker degree = complementary degree
- `h_handshaking`: handshaking lemma (# odd-degree vertices is even)
- `h_boundary_odd`: 1D Tucker on boundary (odd # of boundary odd-degree triangles) -/
theorem tucker_parity_principle
    [Fintype V] [Fintype T] [DecidableEq V] [DecidableEq T]
    [HasBoundary T]
    (K : TriangulatedComplex V T)
    (l : TuckerLabeling V)
    (tuckerDeg : T → ℕ)
    (h_interior_deg : ∀ t, ¬HasBoundary.isBoundary t →
      tuckerDeg t = complementaryDegree K l t)
    (h_handshaking : Even (Finset.univ.filter (fun t => Odd (tuckerDeg t))).card)
    (h_boundary_odd : Odd (Finset.univ.filter (fun t =>
      HasBoundary.isBoundary t ∧ Odd (tuckerDeg t))).card) :
    ∃ t : T, ¬HasBoundary.isBoundary t ∧ hasComplementaryEdge K l t := by
  -- It suffices to show the interior odd-degree set is nonempty
  suffices h_int_odd : Odd (Finset.univ.filter (fun t =>
      ¬HasBoundary.isBoundary t ∧ Odd (tuckerDeg t))).card by
    -- Extract witness from the odd (hence nonempty) set
    have h_pos : 0 < (Finset.univ.filter (fun t =>
        ¬HasBoundary.isBoundary t ∧ Odd (tuckerDeg t))).card := by
      obtain ⟨k, hk⟩ := h_int_odd; omega
    obtain ⟨t, ht⟩ := Finset.card_pos.mp h_pos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    refine ⟨t, ht.1, ?_⟩
    -- Interior triangle with odd Tucker degree has positive complementary degree
    have h_deg_pos : 0 < complementaryDegree K l t := by
      rw [← h_interior_deg t ht.1]; obtain ⟨m, hm⟩ := ht.2; omega
    exact (hasComplementaryEdge_iff_complementaryDegree_pos K l t).mpr h_deg_pos
  -- Partition odd-degree triangles by boundary status: total = boundary + interior
  have h_split : (Finset.univ.filter (fun t => Odd (tuckerDeg t))).card =
      (Finset.univ.filter (fun t => HasBoundary.isBoundary t ∧ Odd (tuckerDeg t))).card +
      (Finset.univ.filter (fun t => ¬HasBoundary.isBoundary t ∧ Odd (tuckerDeg t))).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext t
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    · simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun _ ⟨h1, _⟩ ⟨h2, _⟩ => h2 h1
  -- Parity: even total, odd boundary → odd interior
  exact Nat.odd_iff.mpr (by
    have h1 := Nat.even_iff.mp h_handshaking
    have h2 := Nat.odd_iff.mp h_boundary_odd
    omega)

-- ========================================================================
-- Part VII: Tucker 2D from Parity + 1D Tucker
-- ========================================================================

/-- **Tucker 2D via path-following**: Combine the Tucker graph degree
analysis (handshaking + boundary oddness from 1D Tucker) with the parity
principle to obtain an interior complementary edge. -/
theorem tucker_2d_from_parity
    [Fintype V] [Fintype T] [DecidableEq V] [DecidableEq T]
    [HasBoundary T]
    (K : TriangulatedComplex V T)
    (l : AntipodalTuckerLabeling V)
    (tuckerDeg : T → ℕ)
    (h_interior_deg : ∀ t, ¬HasBoundary.isBoundary t →
      tuckerDeg t = complementaryDegree K l.toTuckerLabeling t)
    (h_handshaking : Even (Finset.univ.filter (fun t => Odd (tuckerDeg t))).card)
    (h_boundary : Odd (Finset.univ.filter (fun t =>
      HasBoundary.isBoundary t ∧ Odd (tuckerDeg t))).card) :
    ∃ v w : V,
      (∃ t : T, ¬HasBoundary.isBoundary t ∧
        ∃ i j : Fin 3, i ≠ j ∧
          K.vertices t i = v ∧ K.vertices t j = w) ∧
      l.label v + l.label w = 0 := by
  obtain ⟨t, hb, hcomp⟩ := tucker_parity_principle K l.toTuckerLabeling
    tuckerDeg h_interior_deg h_handshaking h_boundary
  obtain ⟨i, j, hij, hc⟩ := hcomp
  exact ⟨K.vertices t i, K.vertices t j, ⟨t, hb, i, j, hij, rfl, rfl⟩, hc⟩

-- ========================================================================
-- Part VII: Path-Following Algorithm (Description)
-- ========================================================================

/-
## The Path-Following Algorithm

The proof is constructive — it actually finds the complementary edge:

1. Start at a boundary complementary edge e₀ (exists by 1D Tucker)
2. e₀ belongs to exactly one boundary triangle t₁
3. If t₁ has exactly 1 complementary edge (the boundary one), done: t₁'s
   interior edges provide no path, contradicting parity — so we look elsewhere
4. If t₁ has 2 complementary edges, the second one e₁ is shared with t₂
5. Follow the path: t₁ → t₂ → t₃ → ...
6. The path terminates (finite complex, no revisits since degree ≤ 2)
7. The terminal triangle has degree 1 (enters but doesn't exit)
8. If it's interior, we found our complementary edge ✓

**Key invariant**: The path visits each triangle at most once (since each
has at most 2 complementary edges, entering through one means at most one exit).

This is essentially a walk in a graph of maximum degree 2 — it must
terminate at a vertex of degree 1. The boundary provides one such vertex;
the parity argument guarantees another (interior) one.
-/

-- ========================================================================
-- Part VIII: Concrete Example
-- ========================================================================

/-
Example: Minimal triangulation of a disk with 5 vertices and 3 triangles.

Vertices: A(1), B(-1), C(2), D(-2), E(1)
(boundary: A → B → C → D → E → A, with antipodal labels)

Triangles: △ABE, △BCE, △CDE

Boundary complementary edges:
- AB: label(A) + label(B) = 1 + (-1) = 0 ✓ (complementary)
- CD: label(C) + label(D) = 2 + (-2) = 0 ✓ (complementary)
- BC, DE, EA: not complementary

Count = 2 (even in this case, so parity principle doesn't directly apply)

For Tucker to work, we need an antipodal triangulation — the boundary
must have an odd number of complementary edges, which requires careful
triangulation that respects the antipodal structure.
-/

-- ========================================================================
-- Part IX: SimpleGraph Handshaking → Even Odd-Degree Count
-- ========================================================================

/-
## Connecting to Mathlib: Graph Handshaking Eliminates a Hypothesis

The `tucker_parity_principle` above requires three hypotheses:
1. `h_interior_deg`: interior Tucker degree = complementary degree
2. `h_handshaking`: the number of odd-degree triangles is even
3. `h_boundary_odd`: boundary has odd number of odd-degree triangles

Hypothesis (2) is redundant when the Tucker graph is a `SimpleGraph`:
Mathlib's handshaking lemma (`sum_degrees_eq_twice_card_edges`) implies
that any finite simple graph has an even number of odd-degree vertices.

This reduces Tucker's lemma to just two hypotheses:
- Interior degree correspondence (structural)
- Boundary oddness (from 1D Tucker)
-/

/-- Sum of values mod 2 equals count mod 2 when all values satisfy `f i % 2 = 1`. -/
private theorem sum_mod2_eq_card_mod2 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℕ)
    (h : ∀ i ∈ s, f i % 2 = 1) :
    (∑ i ∈ s, f i) % 2 = s.card % 2 := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    have := h _ (Finset.mem_insert_self _ _)
    have := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    omega

/-- Sum of values mod 2 is 0 when all values satisfy `f i % 2 = 0`. -/
private theorem sum_mod2_eq_zero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℕ)
    (h : ∀ i ∈ s, f i % 2 = 0) :
    (∑ i ∈ s, f i) % 2 = 0 := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have := h _ (Finset.mem_insert_self _ _)
    have := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    omega

/-- The number of odd-degree vertices in any finite simple graph is even.

By the handshaking lemma, `∑ v, G.degree v = 2|E|` (even).
Splitting by degree parity: the even-degree sum is even, the odd-degree
sum has the same parity as its count, so the count must be even. -/
theorem even_card_odd_degree_vertices
    [Fintype T] [DecidableEq T]
    (G : SimpleGraph T) [DecidableRel G.Adj] :
    Even (Finset.univ.filter (fun v : T => Odd (G.degree v))).card := by
  -- Convert Odd to % 2 = 1 for decidability
  simp_rw [Nat.odd_iff]
  rw [Nat.even_iff]
  -- Partition vertices into odd-degree (% 2 = 1) and even-degree (% 2 = 0)
  set S₁ := Finset.univ.filter (fun v : T => G.degree v % 2 = 1) with hS₁_def
  set S₀ := Finset.univ.filter (fun v : T => G.degree v % 2 = 0) with hS₀_def
  -- S₁ and S₀ are disjoint and cover univ
  have hdisjoint : Disjoint S₁ S₀ := by
    rw [Finset.disjoint_filter]
    exact fun v _ h1 h0 => by omega
  have hunion : S₁ ∪ S₀ = Finset.univ := by
    ext v; constructor
    · intro _; exact Finset.mem_univ v
    · intro _; simp only [hS₁_def, hS₀_def, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and]; omega
  -- Total degree sum is even (handshaking lemma)
  have hsum := G.sum_degrees_eq_twice_card_edges
  have htot : (∑ v : T, G.degree v) % 2 = 0 := by omega
  -- Split sum into two parts
  have hsplit : ∑ v : T, G.degree v =
      (∑ v ∈ S₁, G.degree v) + (∑ v ∈ S₀, G.degree v) := by
    rw [← Finset.sum_union hdisjoint, hunion]
  -- Even-degree sum ≡ 0 (mod 2)
  have heven : (∑ v ∈ S₀, G.degree v) % 2 = 0 :=
    sum_mod2_eq_zero _ _ (fun v hv =>
      (Finset.mem_filter.mp hv).2)
  -- Odd-degree sum ≡ count (mod 2)
  have hodd : (∑ v ∈ S₁, G.degree v) % 2 = S₁.card % 2 :=
    sum_mod2_eq_card_mod2 _ _ (fun v hv =>
      (Finset.mem_filter.mp hv).2)
  omega

-- ========================================================================
-- Part X: Tucker Parity with Graph-Derived Handshaking
-- ========================================================================

/-- **Strengthened Tucker parity**: the handshaking hypothesis is derived
from graph structure rather than assumed.

Given a `SimpleGraph T` representing the Tucker graph (where edges connect
triangles sharing a complementary edge), the handshaking lemma
(`∑ degrees = 2|E|`) automatically implies the parity condition.

This reduces Tucker's parity argument to just two hypotheses:
1. Interior degree correspondence (G.degree = complementaryDegree)
2. Boundary oddness (from 1D Tucker on the boundary) -/
theorem tucker_parity_from_graph
    [Fintype V] [Fintype T] [DecidableEq V] [DecidableEq T]
    [HasBoundary T]
    (K : TriangulatedComplex V T) (l : TuckerLabeling V)
    (G : SimpleGraph T) [DecidableRel G.Adj]
    (h_interior_deg : ∀ t, ¬HasBoundary.isBoundary t →
      G.degree t = complementaryDegree K l t)
    (h_boundary_odd : Odd (Finset.univ.filter (fun t =>
      HasBoundary.isBoundary t ∧ Odd (G.degree t))).card) :
    ∃ t : T, ¬HasBoundary.isBoundary t ∧ hasComplementaryEdge K l t :=
  tucker_parity_principle K l (fun t => G.degree t) h_interior_deg
    (even_card_odd_degree_vertices G) h_boundary_odd

-- ========================================================================
-- Verification
-- ========================================================================

#check isComplementary_symm
#check antipodal_complementary
#check complementary_pairs
#check complementaryDegree
#check hasComplementaryEdge_iff_complementaryDegree_pos
#check tucker_parity_principle
#check tucker_2d_from_parity
#check even_card_odd_degree_vertices
#check tucker_parity_from_graph

end TuckerPathFollowing
