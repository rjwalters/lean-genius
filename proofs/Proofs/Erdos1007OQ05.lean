/-
# Erdős #1007 OQ-05: Axiom Elimination for Graph Dimension

## Open Question
"Can the axioms in this formalization (particularly min_edges_dimension_4 and
the existence/uniqueness results) be proved or reduced?"

## Analysis

### Axiom 1: hasUnitEmbedding_exists (PROVED below)
Every finite graph admits a unit distance embedding in ℝⁿ for some n.
Construction: place vertex v at (1/√2)·e_{φ(v)} in ℝ^|V|, where φ : V ≃ Fin |V|.
All distinct pairs are at distance 1, so all edges are unit distance.

NOTE: The original axiom is false for graphs with self-loops (adj v v implies
dist(v,v) = 0 ≠ 1). We prove the corrected version with irreflexivity.
The downstream usage (completeBipartiteAdj) is irreflexive, so this is fine.

### Axiom 2: min_edges_dimension_4 (DEEP — House 2013)
The minimum edges for a dimension-4 graph is ≥ 9. This is the main theorem
of House (2013), "A 4-dimensional graph has at least 9 edges". The proof
requires case analysis on graph structure and geometric rigidity arguments.
Cannot be formalized without substantial infrastructure.

### Axiom 3: k33_unique_minimum (DEEP — House 2013)
K_{3,3} is the UNIQUE graph achieving the minimum. Even harder than axiom 2.
Requires showing all other 9-edge graphs have dimension ≤ 3.

### Axiom 4: min_edges_dimension_5 (DEEP — Chaffee-Noble 2016)
The minimum edges for a dimension-5 graph is ≥ 15. Proved by Chaffee and
Noble in 2016, extending House's methods.

## Status
- [x] Axiom 1: PROVED (with irreflexivity hypothesis)
- [ ] Axiom 2: DEEP (House 2013)
- [ ] Axiom 3: DEEP (House 2013)
- [ ] Axiom 4: DEEP (Chaffee-Noble 2016)
-/

import Mathlib
import Proofs.Erdos1007Problem

open Finset

namespace Erdos1007OQ05

/-! ## Proving hasUnitEmbedding_exists

The key idea: place each vertex at a scaled standard basis vector in ℝ^|V|.
Scaling by 1/√2 makes all inter-vertex distances exactly 1. -/

/-- Helper: squared distance between scaled basis vectors at distinct positions. -/
private lemma scaled_basis_sq_dist {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Finset.univ.sum (fun k : Fin n =>
      ((if i = k then (1 : ℝ) / Real.sqrt 2 else 0) -
       (if j = k then 1 / Real.sqrt 2 else 0)) ^ 2) = 1 := by
  -- The sum has exactly two non-zero terms: at k = i and k = j
  -- At k = i: (1/√2 - 0)² = 1/2
  -- At k = j: (0 - 1/√2)² = 1/2
  -- All other terms are 0
  have h1 : ∀ k : Fin n, k ≠ i → k ≠ j →
      ((if i = k then (1 : ℝ) / Real.sqrt 2 else 0) -
       (if j = k then 1 / Real.sqrt 2 else 0)) ^ 2 = 0 := by
    intro k hki hkj
    simp [Ne.symm hki, Ne.symm hkj]
  -- Rewrite the sum extracting the two non-zero terms
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ j⟩)]
  -- Simplify the term at i
  simp only [if_true, eq_self_iff_true, hij, if_false, Ne.symm hij]
  -- Simplify the term at j
  simp only [hij.symm, if_false, eq_self_iff_true, if_true]
  -- The remaining sum is 0
  have hrest : (Finset.univ.erase i).erase j |>.sum
      (fun k => ((if i = k then (1 : ℝ) / Real.sqrt 2 else 0) -
                 (if j = k then 1 / Real.sqrt 2 else 0)) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_erase] at hk
    have hkj : k ≠ j := hk.1
    have hki : k ≠ i := by
      rw [Finset.mem_erase] at hk
      exact (Finset.mem_erase.mp hk.2).1
    exact h1 k hki hkj
  rw [hrest, add_zero]
  -- Now compute: (1/√2)² + (0 - 1/√2)² = 1/2 + 1/2 = 1
  have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt2_pos
  have h_sq : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
    rw [div_pow, one_pow, sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [sub_zero, zero_sub, neg_sq]
  linarith [h_sq]

/-- Every finite graph with irreflexive adjacency admits a unit distance
    embedding in ℝ^|V|, using scaled standard basis vectors.

    This proves (a corrected version of) the hasUnitEmbedding_exists axiom
    from Erdos1007Problem.lean. The correction adds irreflexivity, which is
    necessary: for any self-loop adj v v, dist(v,v) = 0 ≠ 1. -/
theorem hasUnitEmbedding_exists_irr (V : Type*) [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) (hirr : ∀ v, ¬adj v v) :
    ∃ n, hasUnitEmbedding V adj n := by
  use Fintype.card V
  set φ := Fintype.equivFin V
  refine ⟨⟨fun v i => if φ v = i then 1 / Real.sqrt 2 else 0, ?_⟩⟩
  intro u v hadj
  have huv : u ≠ v := fun h => hirr v (h ▸ hadj)
  have hφ : φ u ≠ φ v := fun h => huv (φ.injective h)
  rw [scaled_basis_sq_dist hφ]
  exact Real.sqrt_one

/-- The completeBipartiteAdj is irreflexive (no self-loops). -/
theorem completeBipartiteAdj_irrefl (m n : ℕ) (v : Fin m ⊕ Fin n) :
    ¬completeBipartiteAdj m n v v := by
  cases v <;> simp [completeBipartiteAdj]

/-- Corollary: K_{m,n} admits a unit distance embedding. -/
theorem completeBipartite_has_embedding (m n : ℕ) :
    ∃ d, hasUnitEmbedding (Fin m ⊕ Fin n) (completeBipartiteAdj m n) d :=
  hasUnitEmbedding_exists_irr _ _ (completeBipartiteAdj_irrefl m n)

/-! ## Summary of Axiom Status

The remaining 3 axioms (min_edges_dimension_4, k33_unique_minimum,
min_edges_dimension_5) are deep results requiring:

For min_edges_dimension_4 (House 2013):
- Geometric rigidity analysis of low-edge graphs
- Case analysis showing all ≤8-edge graphs embed in ℝ³
- Construction showing K_{3,3} requires ℝ⁴

For k33_unique_minimum (House 2013):
- All of the above plus uniqueness argument
- Classification of all 9-edge 4-dimensional graphs

For min_edges_dimension_5 (Chaffee-Noble 2016):
- Extension of House's methods to higher dimensions
- K₆ and K_{1,3,3} analysis
-/

end Erdos1007OQ05
