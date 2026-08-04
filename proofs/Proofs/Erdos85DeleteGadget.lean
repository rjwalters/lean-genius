import Proofs.Erdos85ControlledDeletion
import Proofs.Erdos85GadgetExtension

/-!
# Delete-set/add-gadget surgery for Erdős Problem 85

This composes controlled deletion with arbitrary finite-gadget attachment.
Deleting `k` old vertices and adding an `m`-vertex gadget changes the order by
`m-k`.  The degree hypothesis charges every survivor for exactly its deleted
neighbors and credits it for exactly its new gadget neighbors.
-/

open SimpleGraph

namespace Erdos85

/-- **Exact delete-set/add-gadget surgery.**  The compatibility budgets are
the exact `C₄`-freeness conditions for the final graph, while `hcomp` and
`hnew` are its exact old- and new-vertex degree requirements. -/
theorem c4FreeMinDegreeWitness_delete_set_add_gadget
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ D})
    {N k m d : ℕ}
    (hVcard : Fintype.card V = N) (hDcard : D.card = k)
    (hWcard : Fintype.card W = m) (hfinal : 1 ≤ N - k + m)
    (hcompat : GadgetAttachmentCompatible (deleteVertexSetGraph G D) F A)
    (hcomp : ∀ v : {v : V // v ∉ D},
      d ≤ (deleteVertexSetGraph G D).degree v +
        (Finset.univ.filter fun w => v ∈ A w).card)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w) :
    C4FreeMinDegreeWitness (N - k + m) d := by
  let H : SimpleGraph {v : V // v ∉ D} := deleteVertexSetGraph G D
  let P : SimpleGraph ({v : V // v ∉ D} ⊕ W) := attachGadget H F A
  have hHcard : Fintype.card {v : V // v ∉ D} = N - k := by
    rw [Fintype.card_subtype_compl (fun v : V => v ∈ D)]
    simp [hVcard, hDcard]
  have hPcard : Fintype.card ({v : V // v ∉ D} ⊕ W) = N - k + m := by
    simp [hHcard, hWcard]
  letI : Nonempty ({v : V // v ∉ D} ⊕ W) :=
    Fintype.card_pos_iff.mp (hPcard.trans_gt hfinal)
  apply c4FreeMinDegreeWitness_of_card_eq P hPcard
  · apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro u
    rcases u with v | w
    · rw [show P.degree (.inl v) = H.degree v +
          (Finset.univ.filter fun w => v ∈ A w).card by
        exact attachGadget_degree_old H F A v]
      exact hcomp v
    · rw [show P.degree (.inr w) = (A w).card + F.degree w by
        exact attachGadget_degree_new H F A w]
      exact hnew w
  · exact (attachGadget_not_containsC4_iff_compatible H F A).2 hcompat

/-- Original-degree form of the surgery.  A survivor pays exactly once for
each neighbor in the deleted set and receives exactly one degree unit from
each incident gadget vertex. -/
theorem c4FreeMinDegreeWitness_delete_set_add_gadget_of_compensated_degrees
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ D})
    {N k m d : ℕ}
    (hVcard : Fintype.card V = N) (hDcard : D.card = k)
    (hWcard : Fintype.card W = m) (hfinal : 1 ≤ N - k + m)
    (hcompat : GadgetAttachmentCompatible (deleteVertexSetGraph G D) F A)
    (hcomp : ∀ v : {v : V // v ∉ D},
      d + (G.neighborFinset v.1 ∩ D).card ≤ G.degree v.1 +
        (Finset.univ.filter fun w => v ∈ A w).card)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w) :
    C4FreeMinDegreeWitness (N - k + m) d := by
  apply c4FreeMinDegreeWitness_delete_set_add_gadget G D F A
    hVcard hDcard hWcard hfinal hcompat
  · intro v
    have hsplit := degree_deleteVertexSetGraph_add G D v
    have hv := hcomp v
    omega
  · exact hnew

/-- Order-raising specialization: delete any `k` vertices and replace them by
a compatible gadget on `k+1` vertices.  This is a general witness-extension
surgery and specializes at `k=1` to delete-one/add-pair repair. -/
theorem c4FreeMinDegreeWitness_succ_of_delete_set_add_gadget
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ D})
    {N k d : ℕ}
    (hVcard : Fintype.card V = N) (hDcard : D.card = k)
    (hWcard : Fintype.card W = k + 1)
    (hcompat : GadgetAttachmentCompatible (deleteVertexSetGraph G D) F A)
    (hcomp : ∀ v : {v : V // v ∉ D},
      d + (G.neighborFinset v.1 ∩ D).card ≤ G.degree v.1 +
        (Finset.univ.filter fun w => v ∈ A w).card)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w) :
    C4FreeMinDegreeWitness (N + 1) d := by
  have hk : k ≤ N := by
    rw [← hDcard, ← hVcard]
    exact Finset.card_le_univ D
  have hw :=
    c4FreeMinDegreeWitness_delete_set_add_gadget_of_compensated_degrees
      G D F A hVcard hDcard hWcard (by omega) hcompat hcomp hnew
  have heq : N - k + (k + 1) = N + 1 := by omega
  rw [← heq]
  exact hw

/-- A uniform delete-`k`/add-`k+1` gadget choice for every witness implies
one-step witness extension.  This is the broad finite-gadget analogue of
`witnessExtension_of_repairSet`. -/
theorem witnessExtension_of_delete_set_add_gadget {n k : ℕ}
    (hsurgery : ∀ d (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      d ≤ G.minDegree → ¬ containsC4 (Fin n) G →
      ∃ D : Finset (Fin n), D.card = k ∧
      ∃ F : SimpleGraph (Fin (k + 1)),
        letI : DecidableRel F.Adj := Classical.decRel F.Adj
        ∃ A : Fin (k + 1) → Finset {v : Fin n // v ∉ D},
          GadgetAttachmentCompatible (deleteVertexSetGraph G D) F A ∧
          (∀ v : {v : Fin n // v ∉ D},
            d + (G.neighborFinset v.1 ∩ D).card ≤ G.degree v.1 +
              (Finset.univ.filter fun w => v ∈ A w).card) ∧
          (∀ w : Fin (k + 1), d ≤ (A w).card + F.degree w)) :
    C4FreeWitnessExtension n := by
  rintro d ⟨G, hdec, hmin, hfree⟩
  letI : DecidableRel G.Adj := hdec
  obtain ⟨D, hDcard, F, hdata⟩ := hsurgery d G hdec hmin hfree
  letI : DecidableRel F.Adj := Classical.decRel F.Adj
  obtain ⟨A, hcompat, hcomp, hnew⟩ := hdata
  exact c4FreeMinDegreeWitness_succ_of_delete_set_add_gadget
    G D F A (by simp) hDcard (by simp) hcompat hcomp hnew

end Erdos85
