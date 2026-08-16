import Proofs.Erdos85OrderFortyNineBooleanTerminal

/-!
# Relabeling the order-49 bit encoding

The `t = 0` cube normalization permutes the forty-two low vertices while
fixing the seven high vertices.  This file isolates the representation-level
part of that argument: every permutation of `Fin 49` can be applied to the
1176-bit edge vector, and reading the resulting vector is definitionally the
original adjacency relation precomposed with the permutation.
-/

namespace Erdos85

open SimpleGraph

/-- The compact bit adjacency is symmetric. -/
theorem orderFortyNineBitAdj_comm (edges : BitVec 1176) (i j : Fin 49) :
    orderFortyNineBitAdj edges i j = orderFortyNineBitAdj edges j i := by
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : j ≠ i := Ne.symm hij
    simp only [orderFortyNineBitAdj, hij, hji, if_false,
      orderFortyNineEdgeIndex]
    rw [min_comm, max_comm]

/-- Regard a compact edge vector as a simple graph. -/
def orderFortyNineBitGraph (edges : BitVec 1176) : SimpleGraph (Fin 49) :=
  SimpleGraph.fromRel fun i j => orderFortyNineBitAdj edges i j = true

instance orderFortyNineBitGraph_decidableAdj (edges : BitVec 1176) :
    DecidableRel (orderFortyNineBitGraph edges).Adj :=
  by
    unfold orderFortyNineBitGraph SimpleGraph.fromRel
    infer_instance

theorem orderFortyNineBitGraph_adj_iff
    (edges : BitVec 1176) (i j : Fin 49) :
    (orderFortyNineBitGraph edges).Adj i j ↔
      orderFortyNineBitAdj edges i j = true := by
  rw [orderFortyNineBitGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hij, h | h⟩
    · exact h
    · simpa [orderFortyNineBitAdj_comm edges i j] using h
  · intro h
    exact ⟨by
      intro hij
      subst j
      simpa [orderFortyNineBitAdj] using h, Or.inl h⟩

/-- Apply a vertex permutation to a compact edge vector. -/
def orderFortyNineRelabelEdges
    (edges : BitVec 1176) (e : Fin 49 ≃ Fin 49) : BitVec 1176 :=
  orderFortyNineGraphEdges (SimpleGraph.comap e (orderFortyNineBitGraph edges))

/-- Reading relabeled edge bits is exactly reading the old edge bits at the
permuted endpoints. -/
theorem orderFortyNineBitAdj_relabelEdges
    (edges : BitVec 1176) (e : Fin 49 ≃ Fin 49) (i j : Fin 49) :
    orderFortyNineBitAdj (orderFortyNineRelabelEdges edges e) i j =
      orderFortyNineBitAdj edges (e i) (e j) := by
  rw [orderFortyNineRelabelEdges, orderFortyNineBitAdj_graphEdges]
  by_cases hij : i = j
  · subst j
    simp [orderFortyNineBitAdj]
  · have heij : e i ≠ e j := fun h => hij (e.injective h)
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, SimpleGraph.comap_adj,
      orderFortyNineBitGraph_adj_iff]

end Erdos85
