import Proofs.Erdos85VertexDeletion
import Proofs.Erdos85PairedWitness

/-!
# Delete-one/add-pair surgery for Erdős Problem 85

Deleting a vertex and replacing it by an adjacent pair raises the order by
one.  The two attachment sets repair the degree of every former neighbour of
the deleted vertex when their union covers that neighbourhood.
-/

open SimpleGraph

namespace Erdos85

theorem attachVertex_degree_some_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (x : V) :
    (attachVertex G S).degree (some x) = G.degree x + if x ∈ S then 1 else 0 := by
  rw [degree, degree]
  by_cases hx : x ∈ S
  · simp only [hx, if_pos]
    have hnone : none ∉ (G.neighborFinset x).map ⟨some, Option.some_injective V⟩ := by simp
    rw [show (attachVertex G S).neighborFinset (some x) =
        insert none ((G.neighborFinset x).map ⟨some, Option.some_injective V⟩) by
      ext y
      rcases y with _ | y <;> simp [hx]]
    simp [hnone]
  · simp only [hx, if_neg, Nat.add_zero]
    rw [show (attachVertex G S).neighborFinset (some x) =
        (G.neighborFinset x).map ⟨some, Option.some_injective V⟩ by
      ext y
      rcases y with _ | y <;> simp [hx]]
    simp

theorem pairedAttachment_degree_old_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) (x : V) :
    (attachVertex (attachVertex G S) (pairedSelector T)).degree (some (some x)) =
      G.degree x + (if x ∈ S then 1 else 0) + (if x ∈ T then 1 else 0) := by
  rw [attachVertex_degree_some_eq, attachVertex_degree_some_eq]
  simp [pairedSelector]

theorem degree_induce_delete_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) (v : {y // y ≠ x}) :
    (G.induce {y | y ≠ x}).degree v = G.degree v - if G.Adj v x then 1 else 0 := by
  let T : Finset V := G.neighborFinset v
  have himage := G.map_neighborFinset_induce (s := {y | y ≠ x}) v
  have hinter : G.neighborFinset v ∩ {y | y ≠ x}.toFinset = T.erase x := by
    ext y
    simp [T, and_comm]
  have hcard : (G.induce {y | y ≠ x}).degree v = (T.erase x).card := by
    rw [degree, ← Finset.card_map]
    rw [himage, hinter]
  rw [hcard]
  by_cases hx : G.Adj v x
  · simp only [hx, if_pos]
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset v x).2 hx)]
    simp [T, SimpleGraph.card_neighborFinset_eq_degree]
  · simp only [hx, if_neg, Nat.sub_zero]
    rw [Finset.erase_eq_of_notMem (fun hmem =>
      hx ((G.mem_neighborFinset v x).1 hmem))]
    simp [T, SimpleGraph.card_neighborFinset_eq_degree]

/-- Delete `x`, then replace it by an adjacent pair attached along `S,T`.
Covering the old neighbourhood of `x` repairs every degree lost in deletion. -/
theorem c4FreeMinDegreeWitness_delete_add_pair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) {n d : ℕ}
    (hcard : Fintype.card V = n + 1) (hmin : d ≤ G.minDegree)
    (hfree : ¬ containsC4 V G)
    (S T : Finset {y : V // y ≠ x})
    (hS : d - 1 ≤ S.card) (hT : d - 1 ≤ T.card) (hd : 1 ≤ d)
    (hcompat : PairedAttachmentCompatible (G.induce {y | y ≠ x}) S T)
    (hrepair : ∀ y : {y : V // y ≠ x},
      G.Adj y x → G.degree y = d → y ∈ S ∪ T) :
    C4FreeMinDegreeWitness (n + 2) d := by
  let H : SimpleGraph {y : V // y ≠ x} := G.induce (fun y => y ≠ x)
  let P : SimpleGraph (Option (Option {y : V // y ≠ x})) :=
    attachVertex (attachVertex H S) (pairedSelector T)
  have hcardH : Fintype.card {y : V // y ≠ x} = n := by
    simp [hcard]
  have hcardP : Fintype.card (Option (Option {y : V // y ≠ x})) = n + 2 := by
    simp [hcardH]
  apply c4FreeMinDegreeWitness_of_card_eq P hcardP
  · apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro u
    rcases u with _ | (_ | y)
    · exact le_degree_secondEndpoint_of_pred_le H S T hT hd
    · exact le_degree_firstEndpoint_of_pred_le H S T hS hd
    · change d ≤ (attachVertex (attachVertex H S) (pairedSelector T)).degree
          (some (some y))
      rw [pairedAttachment_degree_old_eq]
      have hdel : H.degree y = G.degree y - if G.Adj y x then 1 else 0 :=
        degree_induce_delete_eq G x y
      have hydeg : d ≤ G.degree y := hmin.trans (G.minDegree_le_degree y)
      by_cases hyx : G.Adj y x
      · by_cases htight : G.degree y = d
        · have hy := Finset.mem_union.mp (hrepair y hyx htight)
          rw [hdel, if_pos hyx]
          rcases hy with hyS | hyT
          · simp only [hyS, if_pos]
            omega
          · simp only [hyT, if_pos]
            omega
        · rw [hdel, if_pos hyx]
          omega
      · have hold : d ≤ H.degree y := by
          rw [hdel, if_neg hyx, Nat.sub_zero]
          exact hydeg
        exact hold.trans (by omega)
  · apply pairedAttachment_not_containsC4 H S T
    · intro hC4
      rcases hC4 with ⟨f, hf, hadj⟩
      exact hfree ⟨fun i ↦ f i, Subtype.val_injective.comp hf,
        fun i j hij ↦ hadj i j hij⟩
    · exact hcompat

end Erdos85
