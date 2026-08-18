import Proofs.Erdos85Relabel

/-!
# Controlled deletion of a vertex set

Deleting a set D lowers a surviving vertex degree by exactly the number of its
neighbors in D.  Bounding this local incidence can be much sharper than paying
one degree unit for every deleted vertex.
-/

open SimpleGraph

namespace Erdos85

/-- The induced graph obtained by deleting all vertices in D. -/
abbrev deleteVertexSetGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (D : Finset V) :
    SimpleGraph {v : V // v ∉ D} :=
  G.induce {v | v ∉ D}

/-- Exact degree loss under deletion of a finite vertex set. -/
theorem degree_deleteVertexSetGraph_add
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (v : {v : V // v ∉ D}) :
    (deleteVertexSetGraph G D).degree v +
        (G.neighborFinset v ∩ D).card = G.degree v := by
  let N := G.neighborFinset v
  have himage := G.map_neighborFinset_induce (s := {y | y ∉ D}) v
  have hinter :
      G.neighborFinset v ∩ {y | y ∉ D}.toFinset = N \ D := by
    ext y
    simp [N]
  have hdegree :
      (deleteVertexSetGraph G D).degree v = (N \ D).card := by
    rw [SimpleGraph.degree]
    have hc := congrArg Finset.card himage
    simp only [Finset.card_map] at hc
    rw [hinter] at hc
    exact hc
  have hpartition := Finset.card_sdiff_add_card_inter N D
  rw [hdegree]
  calc
    (N \ D).card + (G.neighborFinset v ∩ D).card = N.card := by
      change (N \ D).card + (N ∩ D).card = N.card
      exact hpartition
    _ = G.degree v := by simp [N]

/-- Exact per-vertex form of controlled deletion.  The original degree of each
survivor pays for precisely its number of deleted neighbors. -/
theorem c4FreeMinDegreeWitness_delete_vertex_set_of_compensated_degrees
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) {N k d' : ℕ}
    (hcard : Fintype.card V = N) (hDcard : D.card = k)
    (hremain : 1 ≤ N - k) (hfree : ¬ containsC4 V G)
    (hcomp : ∀ v : {v : V // v ∉ D},
      d' + (G.neighborFinset v ∩ D).card ≤ G.degree v) :
    C4FreeMinDegreeWitness (N - k) d' := by
  let H := deleteVertexSetGraph G D
  have hHcard : Fintype.card {v : V // v ∉ D} = N - k := by
    rw [Fintype.card_subtype_compl (fun v : V => v ∈ D)]
    simp [hcard, hDcard]
  letI : Nonempty {v : V // v ∉ D} :=
    Fintype.card_pos_iff.mp (hHcard.trans_gt (by omega))
  apply c4FreeMinDegreeWitness_of_card_eq H hHcard
  · apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro v
    have hsplit := degree_deleteVertexSetGraph_add G D v
    have hv := hcomp v
    dsimp [H]
    omega
  · rintro ⟨f, hf, hadj⟩
    apply hfree
    exact ⟨fun i => (f i).1, Subtype.val_injective.comp hf,
      fun i j hij => hadj i j hij⟩

/-- Controlled set deletion: if each survivor has at most r neighbors in the
deleted k-set, an order-N degree-d witness yields order N-k and degree d-r. -/
theorem c4FreeMinDegreeWitness_delete_vertex_set
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) {N d k r : ℕ}
    (hcard : Fintype.card V = N) (hDcard : D.card = k)
    (hremain : 1 ≤ N - k)
    (hmin : d ≤ G.minDegree) (hfree : ¬ containsC4 V G)
    (hloss : ∀ v : {v : V // v ∉ D},
      (G.neighborFinset v ∩ D).card ≤ r) :
    C4FreeMinDegreeWitness (N - k) (d - r) := by
  let H := deleteVertexSetGraph G D
  have hHcard : Fintype.card {v : V // v ∉ D} = N - k := by
    rw [Fintype.card_subtype_compl (fun v : V => v ∈ D)]
    simp [hcard, hDcard]
  letI : Nonempty {v : V // v ∉ D} :=
    Fintype.card_pos_iff.mp (hHcard.trans_gt (by omega))
  apply c4FreeMinDegreeWitness_of_card_eq H hHcard
  · apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro v
    have hvdeg := hmin.trans (G.minDegree_le_degree v)
    have hsplit := degree_deleteVertexSetGraph_add G D v
    have hvloss := hloss v
    dsimp [H]
    omega
  · rintro ⟨f, hf, hadj⟩
    apply hfree
    exact ⟨fun i => (f i).1, Subtype.val_injective.comp hf,
      fun i j hij => hadj i j hij⟩

end Erdos85
