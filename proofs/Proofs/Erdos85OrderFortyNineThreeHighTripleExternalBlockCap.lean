import Proofs.Erdos85EncodedExternalBlockCap
import Proofs.Erdos85OrderFortyNineThreeHighTripleCanonicalColorResiduals

namespace Erdos85
open SimpleGraph

/-- The actual special vertices impose block caps on every empty-support vertex. -/
theorem threeHigh_triple_actual_external_block_cap
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G) (z : Fin 49)
    (roots : Fin 3 → Fin 49) (hroots : ∀ k, roots k ∈ threeHighTripleSpecialSet G z)
    (e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49)))
    (hrow : ∀ k i, (e (threeHighEmptyUIndex ((@finProdFinEquiv 3 5) (k,i)))).val ∈
      G.neighborFinset (roots k) ∩ threeHighTripleEmptySet G)
    (B : Fin 24 → Fin 24 → Bool)
    (hB : ∀ x y, decide (G.Adj (e x).val (e y).val) = B x y) :
    encodedExternalBlockCap B threeHighCanonicalRow = true := by
  classical
  apply encodedExternalBlockCap_of_injective_graph G hfree (fun x => (e x).val)
    (fun x y h => e.injective (Subtype.ext h)) roots ?_ B hB threeHighCanonicalRow ?_
  · intro x k he
    have h0 := (Finset.mem_filter.mp (e x).property).2
    have h1 := (Finset.mem_filter.mp (hroots k)).2
    rw [he] at h0
    omega
  · intro k j hj
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hj
    exact (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp (hrow k i)).1

end Erdos85
#print axioms Erdos85.threeHigh_triple_actual_external_block_cap
