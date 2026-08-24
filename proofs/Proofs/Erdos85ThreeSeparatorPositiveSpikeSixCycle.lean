import Proofs.Erdos85ThreeSeparatorNegativeSpikeExclusion
import Proofs.Erdos85BranchDeficitSymmetry

/-! # The six-cycle core of the positive-spike three-separator profile -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Two three-sets with two incidences at every point on one side and at
least two at every point on the other side form a 2-regular bipartite core. -/
theorem two_regular_cross_incidence_of_three_by_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (W P : Finset V) (hWcard : W.card = 3) (hPcard : P.card = 3)
    (hPdeg : ∀ p ∈ P, (G.neighborFinset p ∩ W).card = 2)
    (hWlower : ∀ w ∈ W, 2 ≤ (G.neighborFinset w ∩ P).card) :
    ∀ w ∈ W, (G.neighborFinset w ∩ P).card = 2 := by
  have hcomm := sum_card_neighbor_inter_comm G W P
  have hsumP : (∑ p ∈ P, (G.neighborFinset p ∩ W).card) = 6 := by
    calc
      _ = ∑ _p ∈ P, 2 := by
        apply Finset.sum_congr rfl
        intro p hp
        exact hPdeg p hp
      _ = 6 := by simp [hPcard]
  have hsumW : (∑ w ∈ W, (G.neighborFinset w ∩ P).card) = 6 := by
    rw [hcomm]
    exact hsumP
  intro w hw
  have hwLower := hWlower w hw
  have hrest : 2 * (W.erase w).card ≤
      ∑ u ∈ W.erase w, (G.neighborFinset u ∩ P).card := by
    calc
      2 * (W.erase w).card = ∑ _u ∈ W.erase w, 2 := by
        simp [Nat.mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro u hu
        exact hWlower u (Finset.mem_of_mem_erase hu)
  have hsplit := Finset.sum_erase_add W
    (fun u => (G.neighborFinset u ∩ P).card) hw
  rw [hsumW] at hsplit
  have hEraseCard : (W.erase w).card = 2 := by
    rw [Finset.card_erase_of_mem hw, hWcard]
  omega

/-- In the B7 profile, the three overlap points have pole-degree two; the
q+2 double count at every pole forces the converse degree two as well. -/
theorem positiveSpike_threeSeparator_overlap_is_two_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {q : ℕ}
    (hreg : ∀ v, G.degree v = q)
    (W K R : Finset V) (c : V)
    (hWcard : W.card = 3) (hKRcard : (K ∩ R).card = 3)
    (hcK : c ∈ K) (hcR : c ∉ R)
    (hprofile : ∀ v,
      ((G.neighborFinset v ∩ W).card : ℤ) =
        (if v ∈ K then 1 else 0) + (if v ∈ R then 1 else 0) -
          (if v = c then 1 else 0))
    (hpoleLoad : ∀ w ∈ W,
      (G.neighborFinset w ∩ K).card +
        (G.neighborFinset w ∩ R).card = q + 2) :
    (∀ p ∈ K ∩ R, (G.neighborFinset p ∩ W).card = 2) ∧
      ∀ w ∈ W, (G.neighborFinset w ∩ (K ∩ R)).card = 2 := by
  let P := K ∩ R
  have hPdeg : ∀ p ∈ P, (G.neighborFinset p ∩ W).card = 2 := by
    intro p hp
    have hpK := (Finset.mem_inter.mp hp).1
    have hpR := (Finset.mem_inter.mp hp).2
    have hpc : p ≠ c := by
      intro h
      exact hcR (h ▸ hpR)
    have h := hprofile p
    simp [hpK, hpR, hpc] at h
    exact_mod_cast h
  have hWlower : ∀ w ∈ W, 2 ≤ (G.neighborFinset w ∩ P).card := by
    intro w hw
    let A := G.neighborFinset w ∩ K
    let B := G.neighborFinset w ∩ R
    have hunion : (A ∪ B).card ≤ q := by
      calc
        (A ∪ B).card ≤ (G.neighborFinset w).card := by
          apply Finset.card_le_card
          intro z hz
          rcases Finset.mem_union.mp hz with hz | hz
          · exact (Finset.mem_inter.mp hz).1
          · exact (Finset.mem_inter.mp hz).1
        _ = G.degree w := G.card_neighborFinset_eq_degree w
        _ = q := hreg w
    have hinter : A ∩ B = G.neighborFinset w ∩ P := by
      ext z
      simp [A, B, P, and_left_comm, and_assoc]
    have hcardUnion := Finset.card_union_add_card_inter A B
    rw [hinter] at hcardUnion
    have hload := hpoleLoad w hw
    change A.card + B.card = q + 2 at hload
    omega
  refine ⟨by simpa [P] using hPdeg, ?_⟩
  simpa [P] using two_regular_cross_incidence_of_three_by_three
    G W P hWcard hKRcard hPdeg hWlower

#print axioms two_regular_cross_incidence_of_three_by_three
#print axioms positiveSpike_threeSeparator_overlap_is_two_regular

end

end Erdos85
