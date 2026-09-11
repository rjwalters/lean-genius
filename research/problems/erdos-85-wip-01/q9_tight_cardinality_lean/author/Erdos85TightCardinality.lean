import Proofs.Erdos85DistanceLayers

/-!
# Strict order bound at the C₄-free tight point

The existing friendship-theorem argument on `Fin (k * (k - 1) + 1)` is
transported to arbitrary finite vertex types. Together with the distance-layer
bound, it gives a strict lower bound on the order of every nonempty C₄-free
graph of minimum degree at least `k ≥ 3`. This applies directly to induced
fixed and moved vertex subsets in the automorphism arguments for Erdős 85.
-/

namespace Erdos85

/-- The tight-point obstruction on any finite vertex type. -/
theorem containsC4_of_card_eq_tight_minDegree
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 3 ≤ k)
    (hcard : Fintype.card V = k * (k - 1) + 1)
    (hmin : k ≤ G.minDegree) : containsC4 V G := by
  classical
  let H := G.overFin hcard
  let e : G ≃g H := G.overFinIso hcard
  have hminH : k ≤ H.minDegree := by
    rw [← e.minDegree_eq]
    exact hmin
  obtain ⟨f, hf, hadj⟩ := containsC4_of_tight_minDegree hk H hminH
  refine ⟨fun i => e.symm (f i), e.symm.injective.comp hf, ?_⟩
  intro i j hij
  exact e.symm.map_adj_iff.mpr (hadj i j hij)

/-- A nonempty C₄-free graph lies strictly above the minimum-degree tight point. -/
theorem tight_order_lt_card_of_minDegree
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {k : ℕ} (hk : 3 ≤ k)
    (hmin : k ≤ G.minDegree) :
    k * (k - 1) + 1 < Fintype.card V := by
  classical
  let x : V := Classical.choice inferInstance
  have hbound := one_add_degree_add_mul_sub_two_le_card_of_minDegree G hfree hmin x
  have hdeg : k ≤ G.degree x := hmin.trans (G.minDegree_le_degree x)
  have hmul := Nat.mul_le_mul_right (k - 2) hdeg
  have hsub : k - 1 = (k - 2) + 1 := by omega
  have hle : k * (k - 1) + 1 ≤ Fintype.card V := by
    rw [hsub]
    nlinarith
  have hne : Fintype.card V ≠ k * (k - 1) + 1 := by
    intro heq
    exact hfree (containsC4_of_card_eq_tight_minDegree G hk heq hmin)
  omega

end Erdos85
