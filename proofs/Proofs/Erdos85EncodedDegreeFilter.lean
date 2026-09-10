import Proofs.Erdos85EncodedC4Filter

namespace Erdos85
open SimpleGraph

/-- Executable prescribed-degree test for a Boolean adjacency matrix. -/
def encodedDegreeProfile {W : Type*} [Fintype W]
    (B : W → W → Bool) (d : W → ℕ) : Bool :=
  decide (∀ p, (Finset.univ.filter fun q => B p q).card = d p)

theorem encodedDegreeProfile_of_graph
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (B : W → W → Bool) (d : W → ℕ)
    (hB : ∀ p q, decide (H.Adj p q) = B p q)
    (hd : ∀ p, H.degree p = d p) : encodedDegreeProfile B d = true := by
  apply decide_eq_true_iff.mpr
  intro p
  have hr : (Finset.univ.filter fun q => B p q) = H.neighborFinset p := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← hB,
      decide_eq_true_eq, mem_neighborFinset]
  rw [hr]
  exact hd p

end Erdos85
#print axioms Erdos85.encodedDegreeProfile_of_graph
