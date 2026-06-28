import Mathlib

/-!
# Erdős #1007 OQ-04: The Maximum Dimension of a Graph on n Vertices and m Edges

## Context

`Erdos1007OQ05.lean` / `Erdos1007OQ01.lean` study the **graph dimension** — the least
Euclidean dimension `d` in which a graph has a unit-distance embedding
(`UnitDistanceEmbedding`). They pin down the dimension of the *complete* graph: the
regular simplex gives `dim(Kₙ) = n − 1` (`Erdos1007OQ01.lean`), the sharp simplex bound.

The parent's fourth open question looks past the complete graph:

> *What is the maximum dimension of a graph on `n` vertices and `m` edges? The simplex
> bound gives `dim(Kₙ) = n − 1`, but sparse graphs may also have high dimension.*

So the relevant parameter is not just the vertex count `n` but the **edge count `m`**.
This file supplies the structural facts that frame that question and proves the two
clean, fully-verified bounds available without the deep extremal geometry of House (2013):

* **Subgraph monotonicity** — deleting edges can only *decrease* the dimension. Hence the
  maximum dimension over all graphs on `n` vertices is attained by `Kₙ` (so it equals
  `n − 1`), and more edges never hurt.
* **A vertex-support / edge-count upper bound** — the dimension is controlled by the set
  of vertices that actually carry an edge: if a finite set `S` contains both endpoints of
  every edge, the graph embeds in `ℝ^{|S|}`. In particular a graph with `m` edges has at
  most `2m` non-isolated vertices, so its dimension is at most `2m` — *independent of the
  total vertex count `n`*. This is the precise sense in which a sparse graph cannot have
  dimension much larger than its edge count, even when it has many (isolated) vertices.

The common engine is `hasUnitEmbedding_of_idx`: place vertex `v` at `(1/√2)·e_{idx v}`
for any index map `idx : V → Fin N` that separates the endpoints of every edge. All
distinct scaled basis vectors are at distance `1`, so every edge becomes a unit distance.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`. The
`UnitDistanceEmbedding` structure and `hasUnitEmbedding` predicate mirror
`Erdos1007OQ05.lean` (reproduced locally so the file stands alone; the parent's
`Erdos1007Problem` is bit-rotted under the 4.26.0 toolchain and cannot be imported).
The scaled-basis distance computation `scaled_basis_sq_dist` is reproduced verbatim from
`Erdos1007OQ05.lean`. Everything else is new.
-/

namespace Erdos1007OQ04

open Finset

/-- A unit-distance embedding of a graph in `ℝⁿ` (mirrors
    `Erdos1007OQ05.UnitDistanceEmbedding`). -/
structure UnitDistanceEmbedding (V : Type*) (adj : V → V → Prop) (n : ℕ) where
  embed : V → Fin n → ℝ
  unit_edges : ∀ u v, adj u v →
    Real.sqrt (Finset.univ.sum fun i => (embed u i - embed v i) ^ 2) = 1

/-- A graph can be embedded as unit distances in `ℝⁿ`. -/
def hasUnitEmbedding (V : Type*) (adj : V → V → Prop) (n : ℕ) : Prop :=
  Nonempty (UnitDistanceEmbedding V adj n)

/-! ## The scaled-basis distance computation

`scaled_basis_sq_dist` is reproduced verbatim from `Erdos1007OQ05.lean`: the squared
distance between two scaled standard basis vectors at distinct coordinates is `1`. -/

/-- Helper: squared distance between scaled basis vectors at distinct positions. -/
private lemma scaled_basis_sq_dist {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Finset.univ.sum (fun k : Fin n =>
      ((if i = k then (1 : ℝ) / Real.sqrt 2 else 0) -
       (if j = k then 1 / Real.sqrt 2 else 0)) ^ 2) = 1 := by
  have hc : ((1 : ℝ) / Real.sqrt 2) ^ 2 = 1 / 2 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  -- Each squared difference splits into a contribution at coordinate `i` and at `j`.
  have key : ∀ k : Fin n,
      ((if i = k then (1 : ℝ) / Real.sqrt 2 else 0) -
       (if j = k then 1 / Real.sqrt 2 else 0)) ^ 2
        = (if i = k then (1 : ℝ) / 2 else 0) + (if j = k then 1 / 2 else 0) := by
    intro k
    rcases eq_or_ne i k with hik | hik
    · subst hik
      rw [if_pos rfl, if_neg hij.symm, if_pos rfl, if_neg hij.symm, sub_zero, add_zero, hc]
    · rcases eq_or_ne j k with hjk | hjk
      · subst hjk
        rw [if_neg hik, if_pos rfl, if_neg hik, if_pos rfl, zero_sub, neg_sq, zero_add, hc]
      · rw [if_neg hik, if_neg hjk, if_neg hik, if_neg hjk, sub_zero]
        simp
  rw [Finset.sum_congr rfl (fun k _ => key k), Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  norm_num

/-! ## The index embedding

The single construction underlying every bound below. -/

/-- **Index embedding.** Place vertex `v` at the scaled basis vector `(1/√2)·e_{idx v}` in
    `ℝ^N`. If `idx` sends the two endpoints of every edge to *distinct* coordinates, this
    is a unit-distance embedding: distinct scaled basis vectors are at distance exactly
    `1`. This packages the scaled-basis trick so that every bound below is a one-line
    choice of an index map. -/
theorem hasUnitEmbedding_of_idx {V : Type*} {adj : V → V → Prop} {N : ℕ}
    (idx : V → Fin N) (hsep : ∀ u v, adj u v → idx u ≠ idx v) :
    hasUnitEmbedding V adj N := by
  refine ⟨⟨fun v k => if idx v = k then 1 / Real.sqrt 2 else 0, ?_⟩⟩
  intro u v huv
  rw [scaled_basis_sq_dist (hsep u v huv)]
  exact Real.sqrt_one

/-! ## Subgraph monotonicity

Deleting edges never raises the dimension: the same embedding satisfies fewer
constraints. -/

/-- **Subgraph monotonicity.** If `adj₁` is a subgraph of `adj₂` (every `adj₁`-edge is an
    `adj₂`-edge), any unit embedding of `adj₂` is also one of `adj₁`. So the dimension is
    monotone under edge addition, and the maximum dimension over graphs on a fixed vertex
    set is attained by the complete graph. -/
theorem hasUnitEmbedding_restrict {V : Type*} {adj₁ adj₂ : V → V → Prop} {n : ℕ}
    (hsub : ∀ u v, adj₁ u v → adj₂ u v) (h : hasUnitEmbedding V adj₂ n) :
    hasUnitEmbedding V adj₁ n :=
  h.elim fun e => ⟨⟨e.embed, fun u v huv => e.unit_edges u v (hsub u v huv)⟩⟩

/-! ## Monotonicity in the ambient dimension

Padding with zero coordinates extends an embedding to any higher dimension (reproduced
from `Erdos1007OQ05OQ01.lean` so the edge-count bound can conclude `≤ 2m`). -/

/-- Padding an embedding with zero coordinates extends it from `ℝⁿ` to `ℝᵐ` for `m ≥ n`. -/
def embedding_mono {V : Type*} {adj : V → V → Prop} {n m : ℕ} (hnm : n ≤ m)
    (e : UnitDistanceEmbedding V adj n) : UnitDistanceEmbedding V adj m := by
  classical
  refine ⟨fun v i => if h : (i : ℕ) < n then e.embed v ⟨i, h⟩ else 0, ?_⟩
  intro u v huv
  set G : ℕ → ℝ := fun j =>
    ((if h : j < n then e.embed u ⟨j, h⟩ else 0) - (if h : j < n then e.embed v ⟨j, h⟩ else 0)) ^ 2
    with hG
  have hGzero : ∀ j ∈ range m, j ∉ range n → G j = 0 := by
    intro j _ hj
    simp only [mem_range, not_lt] at hj
    simp only [hG, dif_neg (not_lt.mpr hj), sub_zero]
    ring
  have hsub : range n ⊆ range m := fun x hx =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hnm)
  have hsum : (∑ i : Fin m, G (i : ℕ)) = ∑ i : Fin n, (e.embed u i - e.embed v i) ^ 2 := by
    rw [Fin.sum_univ_eq_sum_range G m,
      (Finset.sum_subset hsub hGzero).symm,
      ← Fin.sum_univ_eq_sum_range G n]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hG, dif_pos i.isLt, Fin.eta]
  rw [hsum]
  exact e.unit_edges u v huv

/-- Monotonicity of `hasUnitEmbedding` in the ambient dimension. -/
theorem hasUnitEmbedding_mono {V : Type*} {adj : V → V → Prop} {n m : ℕ} (hnm : n ≤ m)
    (h : hasUnitEmbedding V adj n) : hasUnitEmbedding V adj m :=
  h.elim fun e => ⟨embedding_mono hnm e⟩

/-! ## The universal bound: dimension ≤ |V|

Indexing all vertices injectively gives an embedding in `ℝ^{|V|}`. -/

/-- **Universal upper bound.** Every loopless graph on a finite vertex set `V` embeds in
    `ℝ^{|V|}` (place vertices at distinct scaled basis vectors). Combined with
    `dim(Kₙ) = n − 1` (the simplex bound, `Erdos1007OQ01.lean`), the maximum dimension of
    a graph on `n` vertices is between `n − 1` and `n`; the sharp value `n − 1` follows
    from the regular-simplex embedding of `Kₙ`. -/
theorem hasUnitEmbedding_card (V : Type*) [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) (hirr : ∀ v, ¬ adj v v) :
    hasUnitEmbedding V adj (Fintype.card V) := by
  refine hasUnitEmbedding_of_idx (Fintype.equivFin V) ?_
  intro u v huv
  have huv' : u ≠ v := fun h => hirr v (h ▸ huv)
  exact fun h => huv' ((Fintype.equivFin V).injective h)

/-! ## The edge-count bound: dimension ≤ |support| ≤ 2·(#edges)

The dimension is controlled by the vertices that actually carry an edge. -/

/-- **Edge-cover bound.** If a finite set `S` contains both endpoints of every edge, the
    graph embeds in `ℝ^{|S|}`. Isolated vertices (those outside `S`) cost no dimension:
    they are all placed at the origin. -/
theorem hasUnitEmbedding_of_cover {V : Type*} [DecidableEq V] {adj : V → V → Prop}
    (hirr : ∀ v, ¬ adj v v) (S : Finset V)
    (hcover : ∀ u v, adj u v → u ∈ S ∧ v ∈ S) :
    hasUnitEmbedding V adj S.card := by
  classical
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · -- `S` empty ⟹ no edges ⟹ embed trivially in `ℝ⁰`.
    have hSempty : S = ∅ := Finset.card_eq_zero.mp h0
    have hempty : ∀ u v, ¬ adj u v := by
      intro u v huv
      have hu := (hcover u v huv).1
      rw [hSempty] at hu
      exact absurd hu (Finset.notMem_empty u)
    rw [h0]
    exact ⟨⟨fun _ i => i.elim0, fun u v huv => absurd huv (hempty u v)⟩⟩
  · haveI : NeZero S.card := ⟨hpos.ne'⟩
    refine hasUnitEmbedding_of_idx
      (fun v => if h : v ∈ S then S.equivFin ⟨v, h⟩ else 0) ?_
    intro u v huv
    obtain ⟨huS, hvS⟩ := hcover u v huv
    have hne : u ≠ v := fun h => hirr v (h ▸ huv)
    simp only [dif_pos huS, dif_pos hvS, ne_eq]
    intro hidx
    exact hne (congrArg Subtype.val (S.equivFin.injective hidx))

/-! ## Edge-count corollary for simple graphs

For a finite simple graph, the incidence support has at most `2·(#edges)` vertices, so the
dimension is at most `2·(#edges)` regardless of how many isolated vertices the graph has. -/

/-- The set of vertices incident to at least one edge of a finite simple graph. -/
noncomputable def support {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter (fun v => ∃ w, G.Adj v w)

/-- **Edge-count upper bound.** A finite simple graph with `m` edges embeds in `ℝ^{2m}`,
    independent of the number of vertices. So a graph's dimension is at most twice its
    edge count: a *sparse* graph has *low* dimension, no matter how large `n` is.

    (The factor `2` is the trivial endpoint count; the sharp constant is the subtler part
    of the open question.) -/
theorem hasUnitEmbedding_two_mul_edges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    hasUnitEmbedding V G.Adj (2 * G.edgeFinset.card) := by
  classical
  -- Every edge endpoint lies in the support `S`.
  have hcover : ∀ u v, G.Adj u v → u ∈ support G ∧ v ∈ support G := by
    intro u v huv
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ u, ⟨v, huv⟩⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ v, ⟨u, huv.symm⟩⟩⟩
  have hbase : hasUnitEmbedding V G.Adj (support G).card :=
    hasUnitEmbedding_of_cover (fun v => G.loopless v) (support G) hcover
  -- The support has at most `2m` vertices: each non-isolated vertex has degree ≥ 1, and
  -- the degrees sum to `2m` (handshake lemma).
  have hle : (support G).card ≤ 2 * G.edgeFinset.card := by
    rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
    calc (support G).card
        = ∑ _v ∈ support G, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ v ∈ support G, G.degree v := by
          refine Finset.sum_le_sum fun v hv => ?_
          rw [support, Finset.mem_filter] at hv
          obtain ⟨w, hvw⟩ := hv.2
          have : 0 < G.degree v := (G.degree_pos_iff_exists_adj v).mpr ⟨w, hvw⟩
          omega
      _ ≤ ∑ v, G.degree v := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  exact hasUnitEmbedding_mono hle hbase

end Erdos1007OQ04

/-!
## Summary

For the dimension of a graph on `n` vertices and `m` edges:

- `hasUnitEmbedding_restrict`: **monotone under edge addition** — fewer edges, lower (or
  equal) dimension; the maximum over all graphs on `n` vertices is realized by `Kₙ`.
- `hasUnitEmbedding_card`: **universal bound `dim ≤ n`** via distinct scaled basis vectors;
  with `dim(Kₙ) = n − 1` (`Erdos1007OQ01.lean`) this places the maximum dimension on `n`
  vertices at exactly `n − 1`.
- `hasUnitEmbedding_of_cover` / `hasUnitEmbedding_two_mul_edges`: **edge-count bound
  `dim ≤ 2m`** — only the non-isolated vertices matter, so a sparse graph has low dimension
  irrespective of `n`. This is the rigorous form of "sparse graphs cannot have *arbitrarily*
  high dimension": their dimension is tied to the edge count, not the vertex count.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/
