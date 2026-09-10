import Proofs.Erdos85EncodedC4Filter

namespace Erdos85
open SimpleGraph

/-- Blocks adjacent to external vertices constrain every encoded vertex's neighborhood. -/
def encodedExternalBlockCap {W K : Type*} [Fintype W] [DecidableEq W] [Fintype K]
    (B : W → W → Bool) (blocks : K → Finset W) : Bool :=
  decide (∀ x k, ((blocks k).filter (fun i => B x i)).card ≤ 1)

theorem encodedExternalBlockCap_of_injective_graph
    {V W K : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [Fintype K]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hfree : ¬ containsC4 V G)
    (f : W → V) (hinj : Function.Injective f) (roots : K → V)
    (hne : ∀ x k, f x ≠ roots k)
    (B : W → W → Bool) (hB : ∀ x y, decide (G.Adj (f x) (f y)) = B x y)
    (blocks : K → Finset W) (hblocks : ∀ k i, i ∈ blocks k → G.Adj (roots k) (f i)) :
    encodedExternalBlockCap B blocks = true := by
  apply decide_eq_true_iff.mpr
  intro x k
  apply Finset.card_le_one.mpr
  intro a ha b hb
  apply hinj
  have hc := (not_containsC4_iff_forall_common_le_one G).mp hfree (f x) (roots k) (hne x k)
  have hm {i : W} (hi : i ∈ (blocks k).filter (fun i => B x i)) :
      f i ∈ G.neighborFinset (f x) ∩ G.neighborFinset (roots k) := by
    obtain ⟨hi,hBi⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset _ _).mpr (of_decide_eq_true ((hB x i).trans hBi)),
        (G.mem_neighborFinset _ _).mpr (hblocks k i hi)⟩
  exact Finset.card_le_one.mp hc (f a) (hm ha) (f b) (hm hb)

end Erdos85
#print axioms Erdos85.encodedExternalBlockCap_of_injective_graph
