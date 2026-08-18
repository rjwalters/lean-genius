import Proofs.Erdos85SevenRegularNearTwinLiteCommutingBalance
import Proofs.Erdos85AlternatingFourthMoment

/-! # General regular-codegree overlap law for commuting graphs -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem sum_mem_indicator_mul_general
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finset V) (f : V → ℤ) :
    (∑ w : V, (if w ∈ P then 1 else 0) * f w) = ∑ w ∈ P, f w := by
  calc
    (∑ w : V, (if w ∈ P then 1 else 0) * f w) =
        ∑ w : V, if w ∈ P then f w else 0 := by
      apply Finset.sum_congr rfl
      intro w _hw
      split <;> simp_all
    _ = ∑ w ∈ P, f w := by
      rw [← Finset.sum_filter]
      simp

private theorem adjMatrix_sum_le_card_general
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (S : Finset V) (z : V) :
    0 ≤ ∑ s ∈ S, R.adjMatrix ℤ s z ∧
      (∑ s ∈ S, R.adjMatrix ℤ s z) ≤ S.card := by
  constructor
  · apply Finset.sum_nonneg
    intro s _hs
    rw [SimpleGraph.adjMatrix_apply]
    split <;> norm_num
  · calc
      (∑ s ∈ S, R.adjMatrix ℤ s z) ≤ ∑ _s ∈ S, (1 : ℤ) := by
        apply Finset.sum_le_sum
        intro s _hs
        rw [SimpleGraph.adjMatrix_apply]
        split <;> norm_num
      _ = S.card := by simp

/-- General private-set normalization in a regular graph. -/
theorem regular_codegree_privateSets
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    {k ell : ℕ} (hreg : ∀ v, D.degree v = k)
    {x y : V}
    (hcommon : (D.neighborFinset x ∩ D.neighborFinset y).card = ell) :
    ∃ P Q : Finset V,
      P.card = k - ell ∧ Q.card = k - ell ∧ Disjoint P Q ∧
      ∀ w : V, D.adjMatrix ℤ x w - D.adjMatrix ℤ y w =
        (if w ∈ P then 1 else 0) - (if w ∈ Q then 1 else 0) := by
  let P := D.neighborFinset x \ D.neighborFinset y
  let Q := D.neighborFinset y \ D.neighborFinset x
  have hxcard : (D.neighborFinset x).card = k := by
    rw [D.card_neighborFinset_eq_degree, hreg x]
  have hycard : (D.neighborFinset y).card = k := by
    rw [D.card_neighborFinset_eq_degree, hreg y]
  have hcommon' : (D.neighborFinset y ∩ D.neighborFinset x).card = ell := by
    simpa [Finset.inter_comm] using hcommon
  have hP : P.card = k - ell := by
    dsimp [P]
    rw [Finset.card_sdiff, hcommon', hxcard]
  have hQ : Q.card = k - ell := by
    dsimp [Q]
    rw [Finset.card_sdiff, hcommon, hycard]
  have hdisj : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro z hzP hzQ
    exact (Finset.mem_sdiff.mp hzP).2 (Finset.mem_sdiff.mp hzQ).1
  refine ⟨P, Q, hP, hQ, hdisj, ?_⟩
  intro w
  rw [SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply]
  have hPmem : w ∈ P ↔ D.Adj x w ∧ ¬D.Adj y w := by
    simp [P, SimpleGraph.mem_neighborFinset]
  have hQmem : w ∈ Q ↔ D.Adj y w ∧ ¬D.Adj x w := by
    simp [Q, SimpleGraph.mem_neighborFinset]
  by_cases hx : D.Adj x w <;> by_cases hy : D.Adj y w <;>
    simp_all

/-- **Regular-codegree commuting overlap law.**  If `D` is `k`-regular and
`x,y` have codegree `λ`, then every graph commuting with `D` has mixed
neighborhood overlap imbalance at most `k-λ`. -/
theorem regular_codegree_commutingGraph_overlapDifference_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (D R : SimpleGraph V) [DecidableRel D.Adj] [DecidableRel R.Adj]
    {k ell : ℕ} (hreg : ∀ v, D.degree v = k)
    {x y : V}
    (hcommon : (D.neighborFinset x ∩ D.neighborFinset y).card = ell)
    (hle : ell ≤ k)
    (hcomm : D.adjMatrix ℤ * R.adjMatrix ℤ =
      R.adjMatrix ℤ * D.adjMatrix ℤ) :
    ∀ z : V,
      |((R.neighborFinset x ∩ D.neighborFinset z).card : ℤ) -
        ((R.neighborFinset y ∩ D.neighborFinset z).card : ℤ)| ≤ k - ell := by
  obtain ⟨P, Q, hP, hQ, _hdisj, hrow⟩ :=
    regular_codegree_privateSets D hreg hcommon
  intro z
  have htransport := finiteSparseRowDifference_of_matrix_comm
    (D.adjMatrix ℤ) (R.adjMatrix ℤ) x y P Q hcomm hrow z
  have hprivate :
      (∑ w : V,
        ((if w ∈ P then 1 else 0) - (if w ∈ Q then 1 else 0)) *
          R.adjMatrix ℤ w z) =
        (∑ p ∈ P, R.adjMatrix ℤ p z) -
          (∑ q ∈ Q, R.adjMatrix ℤ q z) := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib,
      sum_mem_indicator_mul_general P (fun w => R.adjMatrix ℤ w z),
      sum_mem_indicator_mul_general Q (fun w => R.adjMatrix ℤ w z)]
  rw [hprivate] at htransport
  have hmixed :
      (∑ w : V,
        (R.adjMatrix ℤ x w - R.adjMatrix ℤ y w) * D.adjMatrix ℤ w z) =
      ((R.neighborFinset x ∩ D.neighborFinset z).card : ℤ) -
        ((R.neighborFinset y ∩ D.neighborFinset z).card : ℤ) := by
    calc
      _ = (R.adjMatrix ℤ * D.adjMatrix ℤ) x z -
          (R.adjMatrix ℤ * D.adjMatrix ℤ) y z := by
        rw [Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro w _hw
        rw [sub_mul]
      _ = _ := by
        rw [adjMatrix_mul_subgraph_apply_eq_card_mixed,
          adjMatrix_mul_subgraph_apply_eq_card_mixed]
  rw [hmixed] at htransport
  have hPb := adjMatrix_sum_le_card_general R P z
  have hQb := adjMatrix_sum_le_card_general R Q z
  rw [hP] at hPb
  rw [hQ] at hQb
  rw [← htransport]
  apply abs_le.mpr
  have hcast : (((k - ell : ℕ) : ℤ)) = (k : ℤ) - ell := by
    rw [Nat.cast_sub hle]
  constructor <;> omega

end

end Erdos85
