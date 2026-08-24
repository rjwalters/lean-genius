import Proofs.Erdos85FinalDyadicEmptyBlockSecondLayerHalf

/-!
# Exceptional-support bound from one empty second layer

The punctured neighbor branches around an empty center are disjoint and have
total size `q(q-1)`.  They all have half occupancy, leaving room for at most
`q` exceptional centers in square order.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The existence of an empty center in the empty-center defect clique forces
the final-dyadic exceptional support to have size at most `q`. -/
theorem finalDyadic_exceptionalSignedSupport_card_le_q_of_emptyCenter
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j : ℕ}
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    {e : V} (he : e ∈ emptyLineCenters G S) :
    (exceptionalSignedSupport G S q).card ≤ q := by
  let B := G.neighborFinset e
  let U := B.biUnion (fun x => (G.neighborFinset x).erase e)
  let C := exceptionalSignedSupport G S q
  have hpair : (↑B : Set V).PairwiseDisjoint
      (fun x => (G.neighborFinset x).erase e) := by
    intro x hx y hy hxy
    change Disjoint ((G.neighborFinset x).erase e)
      ((G.neighborFinset y).erase e)
    rw [Finset.disjoint_left]
    intro z hzx hzy
    have hzxData := Finset.mem_erase.mp hzx
    have hzyData := Finset.mem_erase.mp hzy
    have hex : G.Adj e x := (G.mem_neighborFinset e x).mp hx
    have hey : G.Adj e y := (G.mem_neighborFinset e y).mp hy
    have hxz : G.Adj x z := (G.mem_neighborFinset x z).mp hzxData.2
    have hyz : G.Adj y z := (G.mem_neighborFinset y z).mp hzyData.2
    exact hfree (containsC4_of_two_common hxy hzxData.1.symm
      hex hey hxz.symm hyz.symm)
  have hUcard : U.card = q * (q - 1) := by
    dsimp only [U]
    rw [Finset.card_biUnion hpair]
    calc
      (∑ x ∈ B, ((G.neighborFinset x).erase e).card) =
          ∑ _x ∈ B, (q - 1) := by
            apply Finset.sum_congr rfl
            intro x hx
            have hex : e ∈ G.neighborFinset x :=
              (G.mem_neighborFinset x e).mpr
                ((G.mem_neighborFinset e x).mp hx).symm
            rw [Finset.card_erase_of_mem hex,
              G.card_neighborFinset_eq_degree, hreg]
      _ = B.card * (q - 1) := by simp
      _ = q * (q - 1) := by
        dsimp only [B]
        rw [G.card_neighborFinset_eq_degree, hreg]
  have hUhalf : ∀ z ∈ U, (G.neighborFinset z ∩ S).card = 2 ^ j := by
    intro z hz
    obtain ⟨x, hx, hzx⟩ := Finset.mem_biUnion.mp hz
    have hzxData := Finset.mem_erase.mp hzx
    exact finalDyadic_emptyCenter_puncturedSecondLayer_occupancy_eq_half
      G hfree hqa hreg S hdiv hemptyClique he hx hzxData.2 hzxData.1
  have hdisj : Disjoint U C := by
    rw [Finset.disjoint_left]
    intro z hzU hzC
    have hzHalf := hUhalf z hzU
    have hzSupport : z ∈ fullLineCenters G S q ∪ emptyLineCenters G S := by
      rw [← exceptionalSignedSupport_eq_full_union_empty G S q]
      exact hzC
    rcases Finset.mem_union.mp hzSupport with hzFull | hzEmpty
    · have hzq := (mem_fullLineCenters G S q z).mp hzFull
      rw [hqa] at hzq
      have hpowPos : 0 < 2 ^ j := by positivity
      have hne : 2 ^ j ≠ 2 * 2 ^ j := by omega
      exact hne (hzHalf.symm.trans hzq)
    · have hzzero := (mem_emptyLineCenters G S z).mp hzEmpty
      have hpowPos : 0 < 2 ^ j := by positivity
      exact (Nat.ne_of_gt hpowPos) (hzHalf.symm.trans hzzero)
  have hunionSub : U ∪ C ⊆ (Finset.univ : Finset V) :=
    Finset.subset_univ _
  have htotal : U.card + C.card ≤ Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hdisj]
    simpa using Finset.card_le_card hunionSub
  rw [hUcard, hcard] at htotal
  change C.card ≤ q
  have hqpos : 0 < q := by rw [hqa]; positivity
  have hsplit : q * (q - 1) + q = q * q := by
    calc
      q * (q - 1) + q = q * ((q - 1) + 1) := by ring
      _ = q * q := by rw [Nat.sub_add_cancel hqpos]
  omega

end


end Erdos85

#print axioms
  Erdos85.finalDyadic_exceptionalSignedSupport_card_le_q_of_emptyCenter
