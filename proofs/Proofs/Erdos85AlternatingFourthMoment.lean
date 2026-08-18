import Proofs.Erdos85C4FreeFourthMoment

/-!
# Alternating fourth moments inside a `C₄`-free graph

Let `T` be any spanning subgraph of a `C₄`-free graph `G`, with adjacency
matrices `T` and `A`.  Then

`tr(A T A T) = tr(T⁴)`.

For distinct endpoints, an `A`--`T` two-walk and a `T`--`A` two-walk both
lie in the common-neighbor set in `G`, which has cardinality at most one.
Consequently, if both walks exist then their middle vertices agree and both
edges are in `T`.  On the diagonal all three counts equal `deg_T`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A mixed adjacency product counts mixed common neighbors. -/
theorem adjMatrix_mul_subgraph_apply_eq_card_mixed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G T : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel T.Adj]
    (x y : V) :
    (G.adjMatrix ℤ * T.adjMatrix ℤ) x y =
      ((G.neighborFinset x ∩ T.neighborFinset y).card : ℤ) := by
  rw [G.adjMatrix_mul_apply]
  simp only [SimpleGraph.adjMatrix_apply]
  rw [Finset.sum_boole]
  apply congrArg (fun s : Finset V => (s.card : ℤ))
  ext z
  simp [SimpleGraph.mem_neighborFinset, T.adj_comm]

private theorem mixed_common_card_product
    {V : Type*} [Fintype V] [DecidableEq V]
    (G T : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel T.Adj]
    (hfree : ¬ containsC4 V G) (hTG : T ≤ G) (x y : V) :
    (G.neighborFinset x ∩ T.neighborFinset y).card *
        (T.neighborFinset x ∩ G.neighborFinset y).card =
      (T.neighborFinset x ∩ T.neighborFinset y).card ^ 2 := by
  classical
  let S := G.neighborFinset x ∩ T.neighborFinset y
  let R := T.neighborFinset x ∩ G.neighborFinset y
  let U := T.neighborFinset x ∩ T.neighborFinset y
  by_cases hxy : x = y
  · subst y
    have hTxG : T.neighborFinset x ⊆ G.neighborFinset x := by
      intro z hz
      exact (G.mem_neighborFinset x z).mpr
        (hTG ((T.mem_neighborFinset x z).mp hz))
    have hS : S = T.neighborFinset x := by
      dsimp [S]
      exact Finset.inter_eq_right.mpr hTxG
    have hR : R = T.neighborFinset x := by
      dsimp [R]
      exact Finset.inter_eq_left.mpr hTxG
    have hU : U = T.neighborFinset x := by
      dsimp [U]
      rw [Finset.inter_self]
    change S.card * R.card = U.card ^ 2
    rw [hS, hR, hU, pow_two]
  · let K := G.neighborFinset x ∩ G.neighborFinset y
    have hK : K.card ≤ 1 := by
      exact common_le_one_of_not_containsC4 hfree x y hxy
    have hSK : S ⊆ K := by
      intro z hz
      have hz' := Finset.mem_inter.mp hz
      exact Finset.mem_inter.mpr ⟨hz'.1,
        (G.mem_neighborFinset y z).mpr
          (hTG ((T.mem_neighborFinset y z).mp hz'.2))⟩
    have hRK : R ⊆ K := by
      intro z hz
      have hz' := Finset.mem_inter.mp hz
      exact Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset x z).mpr
          (hTG ((T.mem_neighborFinset x z).mp hz'.1)), hz'.2⟩
    have hUS : U ⊆ S := by
      intro z hz
      have hz' := Finset.mem_inter.mp hz
      exact Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset x z).mpr
          (hTG ((T.mem_neighborFinset x z).mp hz'.1)), hz'.2⟩
    have hUR : U ⊆ R := by
      intro z hz
      have hz' := Finset.mem_inter.mp hz
      exact Finset.mem_inter.mpr ⟨hz'.1,
        (G.mem_neighborFinset y z).mpr
          (hTG ((T.mem_neighborFinset y z).mp hz'.2))⟩
    have hSle : S.card ≤ 1 := le_trans (Finset.card_le_card hSK) hK
    have hRle : R.card ≤ 1 := le_trans (Finset.card_le_card hRK) hK
    have hUle : U.card ≤ 1 := le_trans (Finset.card_le_card hUS) hSle
    have hboth : S.card = 1 → R.card = 1 → U.card = 1 := by
      intro hSone hRone
      obtain ⟨s, hs⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
      obtain ⟨r, hr⟩ := Finset.card_pos.mp (by omega : 0 < R.card)
      have hsr : s = r := by
        have hsK := hSK hs
        have hrK := hRK hr
        by_contra hne
        have htwo : 2 ≤ K.card := by
          apply Finset.one_lt_card.mpr
          exact ⟨s, hsK, r, hrK, hne⟩
        omega
      subst r
      have hs' := Finset.mem_inter.mp hs
      have hr' := Finset.mem_inter.mp hr
      have hsU : s ∈ U := Finset.mem_inter.mpr ⟨hr'.1, hs'.2⟩
      have hpos : 0 < U.card := Finset.card_pos.mpr ⟨s, hsU⟩
      omega
    have hUtoS : U.card ≤ S.card := Finset.card_le_card hUS
    have hUtoR : U.card ≤ R.card := Finset.card_le_card hUR
    interval_cases hScard : S.card <;>
      interval_cases hRcard : R.card <;>
      interval_cases hUcard : U.card <;>
      simp_all [pow_two]

/-- Pointwise form of the alternating fourth-moment identity. -/
theorem adj_mul_subgraph_entry_product_eq_subgraph_sq_entry_product
    {V : Type*} [Fintype V] [DecidableEq V]
    (G T : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel T.Adj]
    (hfree : ¬ containsC4 V G) (hTG : T ≤ G) (x y : V) :
    (G.adjMatrix ℤ * T.adjMatrix ℤ) x y *
        (G.adjMatrix ℤ * T.adjMatrix ℤ) y x =
      (T.adjMatrix ℤ * T.adjMatrix ℤ) x y *
        (T.adjMatrix ℤ * T.adjMatrix ℤ) y x := by
  rw [adjMatrix_mul_subgraph_apply_eq_card_mixed G T x y,
    adjMatrix_mul_subgraph_apply_eq_card_mixed G T y x,
    adjMatrix_sq_apply_eq_card_common T x y,
    adjMatrix_sq_apply_eq_card_common T y x]
  have hsymmG :
      (G.neighborFinset y ∩ T.neighborFinset x).card =
        (T.neighborFinset x ∩ G.neighborFinset y).card := by
    rw [Finset.inter_comm]
  have hsymmT :
      (T.neighborFinset y ∩ T.neighborFinset x).card =
        (T.neighborFinset x ∩ T.neighborFinset y).card := by
    rw [Finset.inter_comm]
  rw [hsymmG, hsymmT]
  norm_cast
  simpa [pow_two] using mixed_common_card_product G T hfree hTG x y

/-- **Alternating fourth-moment identity.**  Any spanning subgraph of a
`C₄`-free graph has the same `A T A T` trace as its own fourth moment. -/
theorem trace_adj_subgraph_adj_subgraph_eq_trace_subgraph_fourth
    {V : Type*} [Fintype V] [DecidableEq V]
    (G T : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel T.Adj]
    (hfree : ¬ containsC4 V G) (hTG : T ≤ G) :
    Matrix.trace ((G.adjMatrix ℤ * T.adjMatrix ℤ) *
        (G.adjMatrix ℤ * T.adjMatrix ℤ)) =
      Matrix.trace ((T.adjMatrix ℤ * T.adjMatrix ℤ) *
        (T.adjMatrix ℤ * T.adjMatrix ℤ)) := by
  rw [Matrix.trace, Matrix.trace]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Matrix.diag_apply]
  rw [Matrix.mul_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro y _
  exact adj_mul_subgraph_entry_product_eq_subgraph_sq_entry_product
    G T hfree hTG x y

end

end Erdos85
