import Proofs.Erdos85MovedDegree
import Proofs.Erdos85DistanceLayers

namespace Erdos85

/-- A nonidentity adjacency-preserving map of a C4-free graph of minimum
    degree at least nine moves at least fifty-seven vertices. -/
theorem fiftySeven_le_card_moved
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hmin : 9 ≤ G.minDegree)
    (τ : V → V)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    (hmoved : ∃ x, τ x ≠ x) :
    57 ≤ Fintype.card ({v : V | τ v ≠ v} : Set V) := by
  classical
  let M : Set V := {v : V | τ v ≠ v}
  let H := G.induce M
  have hHfree : ¬ containsC4 M H := by
    rintro ⟨f, hf, hadj⟩
    apply hfree
    exact ⟨fun i => (f i).val, Subtype.val_injective.comp hf,
      fun i j hij => hadj i j hij⟩
  have hHmin : 8 ≤ H.minDegree := by
    have h := minDegree_sub_one_le_moved_minDegree G hfree τ hmap hmoved
    change G.minDegree - 1 ≤ H.minDegree at h
    omega
  obtain ⟨x, hx⟩ := hmoved
  let v : M := ⟨x, hx⟩
  have hdegree : 8 ≤ H.degree v := hHmin.trans (H.minDegree_le_degree v)
  have hbound := one_add_degree_add_mul_sub_two_le_card_of_minDegree H hHfree hHmin v
  norm_num only [Nat.reduceSub] at hbound
  change 57 ≤ Fintype.card M
  omega

end Erdos85
