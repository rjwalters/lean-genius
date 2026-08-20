import Proofs.Erdos85MooreFriendship

/-! # Cubic adjacency entries on edges of a C4-free regular graph -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- On every oriented edge of a `d`-regular C4-free graph, the number of
length-three walks is exactly `2d-1`. -/
theorem c4Free_regular_adjMatrix_cube_apply_of_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (d : ℕ)
    (hreg : ∀ x, G.degree x = d)
    {a b : V} (hab : G.Adj a b) :
    (G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ) a b =
      2 * (d : ℤ) - 1 := by
  classical
  let A := G.adjMatrix ℤ
  have haN : a ∈ G.neighborFinset b :=
    (G.mem_neighborFinset b a).mpr hab.symm
  have hcommonDiag :
      (G.neighborFinset a ∩ G.neighborFinset a).card = d := by
    simp [G.card_neighborFinset_eq_degree, hreg]
  have hcommonOff : ∀ k ∈ (G.neighborFinset b).erase a,
      (G.neighborFinset a ∩ G.neighborFinset k).card = 1 := by
    intro k hk
    have hkN := (Finset.mem_erase.mp hk).2
    have hka : k ≠ a := (Finset.mem_erase.mp hk).1
    have hbCommon : b ∈ G.neighborFinset a ∩ G.neighborFinset k := by
      apply Finset.mem_inter.mpr
      exact ⟨(G.mem_neighborFinset a b).mpr hab,
        (G.mem_neighborFinset k b).mpr
          ((G.mem_neighborFinset b k).mp hkN).symm⟩
    have hpos : 0 < (G.neighborFinset a ∩ G.neighborFinset k).card :=
      Finset.card_pos.mpr ⟨b, hbCommon⟩
    have hle := common_le_one_of_not_containsC4 hfree a k hka.symm
    omega
  have hsum :
      (∑ k ∈ G.neighborFinset b,
        (G.neighborFinset a ∩ G.neighborFinset k).card) =
        2 * d - 1 := by
    have hsplit := Finset.sum_erase_add
      (s := G.neighborFinset b)
      (f := fun k ↦ (G.neighborFinset a ∩ G.neighborFinset k).card)
      haN
    have heraseCard : ((G.neighborFinset b).erase a).card = d - 1 := by
      rw [Finset.card_erase_of_mem haN,
        G.card_neighborFinset_eq_degree, hreg]
    have heraseSum :
        (∑ k ∈ (G.neighborFinset b).erase a,
          (G.neighborFinset a ∩ G.neighborFinset k).card) = d - 1 := by
      calc
        _ = ∑ _k ∈ (G.neighborFinset b).erase a, 1 := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hcommonOff k hk
        _ = d - 1 := by simp [heraseCard]
    rw [heraseSum, hcommonDiag] at hsplit
    omega
  have hdpos : 0 < d := by
    rw [← hreg a, ← G.card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr ⟨b,
      (G.mem_neighborFinset a b).mpr hab⟩
  have hsumZ :
      (∑ k ∈ G.neighborFinset b,
        ((G.neighborFinset a ∩ G.neighborFinset k).card : ℤ)) =
        2 * (d : ℤ) - 1 := by
    calc
      _ = ((∑ k ∈ G.neighborFinset b,
          (G.neighborFinset a ∩ G.neighborFinset k).card : ℕ) : ℤ) := by
            push_cast
            rfl
      _ = ((2 * d - 1 : ℕ) : ℤ) := by rw [hsum]
      _ = 2 * (d : ℤ) - 1 := by omega
  change (A * A * A) a b = _
  rw [Matrix.mul_apply]
  simp only [A, SimpleGraph.adjMatrix_apply]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hfilter : (Finset.univ.filter fun k ↦ G.Adj k b) =
      G.neighborFinset b := by
    ext k
    simp [SimpleGraph.mem_neighborFinset, G.adj_comm]
  rw [hfilter]
  have hentry : ∀ k,
      (G.adjMatrix ℤ * G.adjMatrix ℤ) a k =
        ((G.neighborFinset a ∩ G.neighborFinset k).card : ℤ) := by
    intro k
    exact adjMatrix_sq_apply_eq_card_common G a k
  simpa only [hentry, mul_one] using hsumZ

/-- A diagonal cubic entry counts twice the triangles through its vertex.
C4-freeness makes the neighborhood graph a matching, so this entry is at
most the degree. -/
theorem c4Free_regular_adjMatrix_cube_apply_diag_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (d : ℕ)
    (hreg : ∀ x, G.degree x = d) (a : V) :
    (G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ) a a ≤ d := by
  classical
  let A := G.adjMatrix ℤ
  have hcommon : ∀ k ∈ G.neighborFinset a,
      (G.neighborFinset a ∩ G.neighborFinset k).card ≤ 1 := by
    intro k hk
    have hak : a ≠ k := by
      intro h
      subst k
      exact G.loopless.irrefl a ((G.mem_neighborFinset a a).mp hk)
    exact common_le_one_of_not_containsC4 hfree a k hak
  have hsum :
      (∑ k ∈ G.neighborFinset a,
        ((G.neighborFinset a ∩ G.neighborFinset k).card : ℤ)) ≤ d := by
    calc
      _ ≤ ∑ _k ∈ G.neighborFinset a, (1 : ℤ) := by
        apply Finset.sum_le_sum
        intro k hk
        exact_mod_cast hcommon k hk
      _ = d := by simp [G.card_neighborFinset_eq_degree, hreg]
  change (A * A * A) a a ≤ _
  rw [Matrix.mul_apply]
  simp only [A, SimpleGraph.adjMatrix_apply]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hfilter : (Finset.univ.filter fun k ↦ G.Adj k a) =
      G.neighborFinset a := by
    ext k
    simp [SimpleGraph.mem_neighborFinset, G.adj_comm]
  rw [hfilter]
  have hentry : ∀ k,
      (G.adjMatrix ℤ * G.adjMatrix ℤ) a k =
        ((G.neighborFinset a ∩ G.neighborFinset k).card : ℤ) := by
    intro k
    exact adjMatrix_sq_apply_eq_card_common G a k
  simpa only [hentry, mul_one] using hsum

/-- Every row of the cubic adjacency matrix of a `d`-regular graph sums to
`d^3`, the total number of length-three walks starting at that vertex. -/
theorem regular_adjMatrix_cube_row_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hreg : ∀ x, G.degree x = d) (a : V) :
    (∑ b, (G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ) a b) =
      (d : ℤ) ^ 3 := by
  let A := G.adjMatrix ℤ
  let one : V → ℤ := Function.const V 1
  have hAone : A.mulVec one = (d : ℤ) • one := by
    funext x
    change (G.adjMatrix ℤ).mulVec (Function.const V (1 : ℤ)) x =
      ((d : ℤ) • Function.const V (1 : ℤ)) x
    rw [SimpleGraph.adjMatrix_mulVec_const_apply, mul_one, hreg]
    simp
  have hrow :
      (∑ b, (A * A * A) a b) = ((A * A * A).mulVec one) a := by
    simp [Matrix.mulVec, dotProduct, one]
  rw [hrow, ← Matrix.mulVec_mulVec one (A * A) A, hAone,
    Matrix.mulVec_smul, ← Matrix.mulVec_mulVec one A A, hAone,
    Matrix.mulVec_smul, hAone]
  simp [one, pow_succ, mul_comm]

end

end Erdos85

#print axioms Erdos85.c4Free_regular_adjMatrix_cube_apply_of_adj
#print axioms Erdos85.c4Free_regular_adjMatrix_cube_apply_diag_le
#print axioms Erdos85.regular_adjMatrix_cube_row_sum
