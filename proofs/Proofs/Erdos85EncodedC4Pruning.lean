import Proofs.Erdos85EncodedC4Filter

namespace Erdos85

/-- Every true entry in the partial matrix is retained in the completion. -/
def EncodedSubgraph {W : Type*} (A B : W → W → Bool) : Prop :=
  ∀ p q, A p q = true → B p q = true

theorem encodedC4Free_of_subgraph
    {W : Type*} [Fintype W] [DecidableEq W]
    (A B : W → W → Bool) (hsub : EncodedSubgraph A B)
    (hB : encodedC4Free B = true) : encodedC4Free A = true := by
  simp only [encodedC4Free, decide_eq_true_eq] at hB ⊢
  intro p q hpq
  apply le_trans (Finset.card_le_card ?_) (hB p q hpq)
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true] at hx ⊢
  exact ⟨hsub p x hx.1, hsub q x hx.2⟩

/-- Rejection of a partial matrix rules out every edge-extending completion. -/
theorem encodedC4Free_reject_extension
    {W : Type*} [Fintype W] [DecidableEq W]
    (A B : W → W → Bool) (hsub : EncodedSubgraph A B)
    (hA : encodedC4Free A = false) : encodedC4Free B = false := by
  cases hb : encodedC4Free B
  · rfl
  · have ha := encodedC4Free_of_subgraph A B hsub hb
    rw [hA] at ha
    contradiction

end Erdos85
#print axioms Erdos85.encodedC4Free_of_subgraph
#print axioms Erdos85.encodedC4Free_reject_extension
