import Mathlib

/-!
# Erdős #1007 OQ-05 / OQ-01: Foundations of the Graph Dimension

## Context

`Erdos1007OQ05.lean` studies the **graph dimension** — the minimum Euclidean dimension `n` in
which a graph has a unit-distance embedding (`UnitDistanceEmbedding`). Its first open question
asks whether `min_edges_dimension_4` can be approached **computationally**, by enumerating small
graphs and checking their dimension. Any such procedure needs the basic monotonicity and bound
facts about unit embeddings — which the parent never establishes. This file supplies them.

## What this file proves

* `embedding_mono` / `hasUnitEmbedding_mono`: **monotonicity** — a graph embeddable in `ℝⁿ` is
  embeddable in `ℝᵐ` for every `m ≥ n` (pad the extra coordinates with `0`). So the set of
  admissible dimensions is up-closed, and the dimension is the *minimum* of an up-set.
* `hasUnitEmbedding_zero_of_edgeless`: the edgeless graph embeds in `ℝ⁰` (dimension `0`).
* `no_edge_of_hasUnitEmbedding_zero`: conversely, a graph embeddable in `ℝ⁰` has **no edges** —
  an edge would need two points at distance `1` in a `0`-dimensional space, impossible. So
  dimension `0` ⟺ edgeless.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`. The `UnitDistanceEmbedding`
structure and `hasUnitEmbedding` predicate mirror `Erdos1007Problem.lean`, reproduced locally
because that file is currently bit-rotted under the 4.26.0 toolchain (`Nat.find` `DecidablePred`
synthesis and `LT V` failures) and cannot be imported. These results are about `hasUnitEmbedding`
directly and use no axioms.
-/

namespace Erdos1007OQ05OQ01

open Finset

/-- A unit-distance embedding of a graph in `ℝⁿ` (mirrors `Erdos1007Problem.UnitDistanceEmbedding`). -/
structure UnitDistanceEmbedding (V : Type*) (adj : V → V → Prop) (n : ℕ) where
  embed : V → Fin n → ℝ
  unit_edges : ∀ u v, adj u v →
    Real.sqrt (Finset.univ.sum fun i => (embed u i - embed v i) ^ 2) = 1

/-- A graph can be embedded as unit distances in `ℝⁿ`. -/
def hasUnitEmbedding (V : Type*) (adj : V → V → Prop) (n : ℕ) : Prop :=
  Nonempty (UnitDistanceEmbedding V adj n)

/-- **Monotonicity of unit embeddings.** A unit-distance embedding in `ℝⁿ` extends to one in
    `ℝᵐ` for any `m ≥ n` by padding the new coordinates with `0` (distances are unchanged). -/
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

/-- Monotonicity at the level of `hasUnitEmbedding`. -/
theorem hasUnitEmbedding_mono {V : Type*} {adj : V → V → Prop} {n m : ℕ} (hnm : n ≤ m)
    (h : hasUnitEmbedding V adj n) : hasUnitEmbedding V adj m :=
  h.elim fun e => ⟨embedding_mono hnm e⟩

/-- The edgeless graph embeds in `ℝ⁰`: there are no edge constraints to satisfy. -/
theorem hasUnitEmbedding_zero_of_edgeless {V : Type*} {adj : V → V → Prop}
    (h : ∀ u v, ¬ adj u v) : hasUnitEmbedding V adj 0 :=
  ⟨⟨fun _ _ => 0, fun u v huv => absurd huv (h u v)⟩⟩

/-- Conversely, a graph embeddable in `ℝ⁰` has no edges: an edge would force two points at
    distance `1` in a `0`-dimensional space, but every distance there is `0`. -/
theorem no_edge_of_hasUnitEmbedding_zero {V : Type*} {adj : V → V → Prop}
    (h : hasUnitEmbedding V adj 0) : ∀ u v, ¬ adj u v := by
  obtain ⟨e⟩ := h
  intro u v huv
  have hone := e.unit_edges u v huv
  simp only [Finset.univ_eq_empty, Finset.sum_empty, Real.sqrt_zero] at hone
  exact absurd hone (by norm_num)

/-- **Dimension `0` ⟺ edgeless.** A graph embeds in `ℝ⁰` exactly when it has no edges. -/
theorem hasUnitEmbedding_zero_iff_edgeless {V : Type*} {adj : V → V → Prop} :
    hasUnitEmbedding V adj 0 ↔ ∀ u v, ¬ adj u v :=
  ⟨no_edge_of_hasUnitEmbedding_zero, hasUnitEmbedding_zero_of_edgeless⟩

end Erdos1007OQ05OQ01

/-!
## Summary

Basic structure of the graph dimension, prerequisite to any computational dimension check:

- `embedding_mono` / `hasUnitEmbedding_mono`: unit-embeddability is monotone in the dimension
  (pad coordinates with `0`), so the admissible dimensions form an up-set.
- `hasUnitEmbedding_zero_iff_edgeless`: a graph embeds in `ℝ⁰` iff it is edgeless — the base case
  of the dimension.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/
