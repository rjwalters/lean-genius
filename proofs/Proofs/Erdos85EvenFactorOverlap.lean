import Proofs.Erdos85OutsideReturnGramIdentity

/-! # Even overlap between the internal two-factor and exterior pairs -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The number of `H`-edges at `u` which also belong to `R`. -/
def edgeOverlapDegree {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (u : V) : ℕ :=
  (H.neighborFinset u).filter (fun v ↦ R.Adj u v) |>.card

/-- In a two-factor, even overlap degree means zero or two. -/
theorem edgeOverlapDegree_eq_zero_or_two_of_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (hHdeg : ∀ u, H.degree u = 2)
    (heven : ∀ u, Even (edgeOverlapDegree H R u)) (u : V) :
    edgeOverlapDegree H R u = 0 ∨ edgeOverlapDegree H R u = 2 := by
  have hle : edgeOverlapDegree H R u ≤ 2 := by
    calc
      edgeOverlapDegree H R u ≤ (H.neighborFinset u).card :=
        Finset.card_filter_le _ _
      _ = H.degree u := H.card_neighborFinset_eq_degree u
      _ = 2 := hHdeg u
  obtain ⟨k, hk⟩ := heven u
  omega

/-- If one incident `H`-edge lies in `R`, parity forces both incident
`H`-edges to lie in `R`. -/
theorem all_incident_mem_of_even_edgeOverlap
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (hHdeg : ∀ u, H.degree u = 2)
    (heven : ∀ u, Even (edgeOverlapDegree H R u))
    {u v : V} (hHuv : H.Adj u v) (hRuv : R.Adj u v) :
    ∀ {w : V}, H.Adj u w → R.Adj u w := by
  have hpos : 0 < edgeOverlapDegree H R u := by
    apply Finset.card_pos.mpr
    exact ⟨v, Finset.mem_filter.mpr ⟨
      (H.mem_neighborFinset u v).mpr hHuv, hRuv⟩⟩
  have htwo : edgeOverlapDegree H R u = 2 := by
    rcases edgeOverlapDegree_eq_zero_or_two_of_even H R hHdeg heven u with
      hzero | htwo
    · omega
    · exact htwo
  have hfilterEq :
      (H.neighborFinset u).filter (fun x ↦ R.Adj u x) =
        H.neighborFinset u := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    rw [H.card_neighborFinset_eq_degree, hHdeg u]
    exact le_of_eq htwo.symm
  intro w hHuw
  have hw : w ∈ (H.neighborFinset u).filter (fun x ↦ R.Adj u x) := by
    rw [hfilterEq]
    exact (H.mem_neighborFinset u w).mpr hHuw
  exact (Finset.mem_filter.mp hw).2

/-- Overlap membership propagates across a two-factor edge. -/
theorem edgeOverlap_propagates_across_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (hHdeg : ∀ u, H.degree u = 2)
    (heven : ∀ u, Even (edgeOverlapDegree H R u))
    {u v w : V} (hHuv : H.Adj u v) (hRuv : R.Adj u v)
    (hHvw : H.Adj v w) : R.Adj v w := by
  exact all_incident_mem_of_even_edgeOverlap H R hHdeg heven
    hHuv.symm hRuv.symm hHvw

/-- Diagonal parity of the factored outside return transfers, through
`M = 6J - H(6I+R)`, to parity of the local `H`/`R` edge overlap. -/
theorem even_edgeOverlapDegree_of_even_outsideReturn_diagonal
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Q M : Matrix V V ℂ)
    (hQ : Q = (6 : ℂ) • (1 : Matrix V V ℂ) + R.adjMatrix ℂ)
    (hM : M = (6 : ℂ) •
      (FriendshipTheoremOQ01.onesMatrix V).map (Int.castRingHom ℂ) -
        H.adjMatrix ℂ * Q)
    (hdiag : ∀ u, ∃ k : ℕ, M u u = (2 * k : ℕ)) :
    ∀ u, Even (edgeOverlapDegree H R u) := by
  intro u
  obtain ⟨k, hk⟩ := hdiag u
  have hHQ : (H.adjMatrix ℂ * Q) u u =
      (edgeOverlapDegree H R u : ℂ) := by
    rw [hQ, Matrix.mul_apply]
    calc
      (∑ x, H.adjMatrix ℂ u x *
          ((6 : ℂ) • (1 : Matrix V V ℂ) + R.adjMatrix ℂ) x u) =
          ∑ x : V, if H.Adj u x ∧ R.Adj u x then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hux : H.Adj u x
        · have hxu : x ≠ u := (H.ne_of_adj hux).symm
          by_cases hrux : R.Adj u x <;>
            simp [SimpleGraph.adjMatrix_apply, Matrix.add_apply,
              Matrix.smul_apply, hux, hrux, hxu,
              R.adj_comm]
        · simp [SimpleGraph.adjMatrix_apply, hux]
      _ = (((H.neighborFinset u).filter fun x ↦ R.Adj u x).card : ℂ) := by
        rw [Finset.sum_boole]
        have hfilter :
            Finset.univ.filter (fun x ↦ H.Adj u x ∧ R.Adj u x) =
              (H.neighborFinset u).filter (fun x ↦ R.Adj u x) := by
          ext x
          simp [SimpleGraph.mem_neighborFinset]
        rw [hfilter]
      _ = (edgeOverlapDegree H R u : ℂ) := by rfl
  have hmuu : M u u = 6 - (H.adjMatrix ℂ * Q) u u := by
    rw [hM, Matrix.sub_apply, Matrix.smul_apply]
    simp [FriendshipTheoremOQ01.onesMatrix]
  rw [hk, hHQ] at hmuu
  have hc : (((2 * k + edgeOverlapDegree H R u : ℕ) : ℂ)) = 6 := by
    norm_num at hmuu ⊢
    linear_combination hmuu
  have hn : 2 * k + edgeOverlapDegree H R u = 6 := by
    exact_mod_cast hc
  refine ⟨3 - k, ?_⟩
  omega

end

end Erdos85
