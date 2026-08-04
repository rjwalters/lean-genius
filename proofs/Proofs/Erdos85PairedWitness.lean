import Proofs.Erdos85Extension

/-!
# Finite paired attachment witnesses for Erdős Problem 85

This module transports the connected-pair construction to `Fin (n + 2)` and
packages its degree estimates as a witness-extension theorem.
-/

namespace Erdos85

open SimpleGraph

/-- The canonical equivalence identifying two successive optional vertices
with `Fin (n + 2)`. -/
def pairedFinEquiv (n : ℕ) : Fin (n + 2) ≃ Option (Option (Fin n)) :=
  (finSuccEquiv (n + 1)).trans (Equiv.optionCongr (finSuccEquiv n))

/-- Paired attachment transported to the standard vertex type `Fin (n + 2)`. -/
def pairedAttachFin {n : ℕ} (G : SimpleGraph (Fin n))
    (S T : Finset (Fin n)) : SimpleGraph (Fin (n + 2)) :=
  SimpleGraph.comap (pairedFinEquiv n)
    (attachVertex (attachVertex G S) (pairedSelector T))

instance pairedAttachFinDecidableRel {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (S T : Finset (Fin n)) :
    DecidableRel (pairedAttachFin G S T).Adj :=
  fun u v => inferInstanceAs (Decidable
    ((attachVertex (attachVertex G S) (pairedSelector T)).Adj
      (pairedFinEquiv n u) (pairedFinEquiv n v)))

/-- Degrees do not decrease when the paired graph is transported to `Fin`. -/
theorem pairedAttachFin_degree_ge {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (S T : Finset (Fin n)) (u : Fin (n + 2)) :
    (attachVertex (attachVertex G S) (pairedSelector T)).degree
        (pairedFinEquiv n u) ≤ (pairedAttachFin G S T).degree u := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_card_of_injOn (fun w => (pairedFinEquiv n).symm w)
  · intro w hw
    simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw ⊢
    show (attachVertex (attachVertex G S) (pairedSelector T)).Adj
      (pairedFinEquiv n u) (pairedFinEquiv n ((pairedFinEquiv n).symm w))
    rw [Equiv.apply_symm_apply]
    exact hw
  · intro w₁ _ w₂ _ h
    exact (pairedFinEquiv n).symm.injective h

/-- The first endpoint gets one additional neighbour from the second endpoint,
so `d - 1` old neighbours suffice for degree at least `d`. -/
theorem le_degree_firstEndpoint_of_pred_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V)
    {d : ℕ} (hS : d - 1 ≤ S.card) (hd : 1 ≤ d) :
    d ≤ (attachVertex (attachVertex G S) (pairedSelector T)).degree (some none) := by
  have hcard : d ≤ (pairedSelector S).card :=
    le_card_pairedSelector_of_pred_le S hS hd
  refine le_trans hcard ?_
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_card_of_injOn (Option.map some)
  · intro w hw
    simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset]
    rcases w with _ | x
    · simp
    · simp only [Option.map, attachVertex_adj_some_some,
        attachVertex_adj_none_some]
      simpa using hw
  · intro a _ b _ hab
    exact Option.map_injective (fun _ _ h => Option.some.inj h) hab

/-- C₄-freeness transports along `pairedFinEquiv`. -/
theorem pairedAttachFin_not_containsC4 {n : ℕ} (G : SimpleGraph (Fin n))
    (S T : Finset (Fin n))
    (h : ¬ containsC4 (Option (Option (Fin n)))
      (attachVertex (attachVertex G S) (pairedSelector T))) :
    ¬ containsC4 (Fin (n + 2)) (pairedAttachFin G S T) := by
  rintro ⟨f, hinj, hadj⟩
  exact h ⟨fun i => pairedFinEquiv n (f i),
    (pairedFinEquiv n).injective.comp hinj,
    fun i j hij => hadj i j hij⟩

/-- **Connected-pair witness extension.**  If both attachment sets have at
least `d - 1` vertices, every old and new vertex has degree at least `d`.
Compatibility ensures that the resulting graph remains C₄-free. -/
theorem c4FreeMinDegreeWitness_add_two_of_pairedAttachmentCompatible
    {n d : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hdeg : d ≤ G.minDegree) (hfree : ¬ containsC4 (Fin n) G)
    (S T : Finset (Fin n)) (hS : d - 1 ≤ S.card)
    (hT : d - 1 ≤ T.card) (hd : 1 ≤ d)
    (hcompat : PairedAttachmentCompatible G S T) :
    C4FreeMinDegreeWitness (n + 2) d := by
  refine ⟨pairedAttachFin G S T, inferInstance, ?_, ?_⟩
  · apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro u
    refine le_trans ?_ (pairedAttachFin_degree_ge G S T u)
    rcases h : pairedFinEquiv n u with _ | (_ | x)
    · exact le_degree_secondEndpoint_of_pred_le G S T hT hd
    · exact le_degree_firstEndpoint_of_pred_le G S T hS hd
    · exact le_trans
        (le_trans (le_trans hdeg (G.minDegree_le_degree x))
          (degree_le_attachVertex_degree_some G S x))
        (degree_le_attachVertex_degree_some
          (attachVertex G S) (pairedSelector T) (some x))
  · apply pairedAttachFin_not_containsC4 G S T
    exact pairedAttachment_not_containsC4 G S T hfree hcompat

end Erdos85
