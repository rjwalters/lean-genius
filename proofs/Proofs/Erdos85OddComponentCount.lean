import Proofs.Erdos85OddBoundaryClean
import Proofs.Erdos85ComponentLocalObstruction

/-!
# Odd-degree component counting

The clean odd Moore bound applies separately to every connected component.
Summing it gives the sharper component mass bound
`k * (d(d-1)+4) ≤ |V|`.  In degree seven this forces connectedness below
order 92.
-/

namespace Erdos85

open SimpleGraph

/-- The clean odd-degree lower bound, summed over connected components. -/
theorem connectedComponent_count_mul_oddMoore_le_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (hodd : Odd d)
    (hmin : d ≤ G.minDegree) :
    Fintype.card G.ConnectedComponent * (d * (d - 1) + 4) ≤
      Fintype.card V := by
  classical
  let L := d * (d - 1) + 4
  have hcomponent (c : G.ConnectedComponent) : L ≤ c.supp.ncard := by
    let H := G.induce c.supp
    letI : Nonempty c.supp := Set.nonempty_coe_sort.mpr c.nonempty_supp
    have hfreeH : ¬ containsC4 c.supp H :=
      not_containsC4_induce_connectedComponent G hfree c
    have hminH : d ≤ H.minDegree := by
      apply H.le_minDegree_of_forall_le_degree
      intro x
      rw [degree_induce_connectedComponent_supp G c x]
      exact hmin.trans (G.minDegree_le_degree x.1)
    have hb := mul_pred_add_four_le_card_of_c4Free_minDegree_odd_clean
      H hd hodd hminH hfreeH
    exact hb.trans_eq (by
      simpa [Nat.card_eq_fintype_card] using Nat.card_coe_set_eq c.supp)
  have hparts : (∑ c : G.ConnectedComponent, c.supp.ncard) =
      Fintype.card V := by
    calc
      (∑ c : G.ConnectedComponent, c.supp.ncard) =
          ∑ c : G.ConnectedComponent, Fintype.card c.supp := by
        apply Finset.sum_congr rfl
        intro c _hc
        simpa [Nat.card_eq_fintype_card] using
          (Nat.card_coe_set_eq c.supp).symm
      _ = Fintype.card (Σ c : G.ConnectedComponent, c.supp) :=
        Fintype.card_sigma.symm
      _ = Fintype.card V :=
        (Fintype.card_congr (vertexConnectedComponentEquiv G)).symm
  have hsum : (∑ _c : G.ConnectedComponent, L) ≤
      ∑ c : G.ConnectedComponent, c.supp.ncard :=
    Finset.sum_le_sum fun c _hc ↦ hcomponent c
  rw [hparts] at hsum
  simpa [L, Nat.mul_comm] using hsum

/-- Every degree-seven plateau core below order 92 has a connected
edge-minimal representative. -/
theorem C4PlateauCore.exists_connected_degreeSeven_representative
    {m : ℕ} (hm : 4 ≤ m) (hm92 : m < 92)
    (hcore : C4PlateauCore m 7) :
    ∃ (G : SimpleGraph (Fin m)) (_ : DecidableRel G.Adj),
      G.minDegree = 7 ∧ ¬ containsC4 (Fin m) G ∧
      Fintype.card G.ConnectedComponent = 1 := by
  rcases hcore with ⟨G, hdec, hmin, hfree, _hcover, _hnext⟩
  letI : DecidableRel G.Adj := hdec
  have hmass := connectedComponent_count_mul_oddMoore_le_card
    G hfree (d := 7) (by norm_num) (by norm_num) hmin.ge
  have hkpos : 0 < Fintype.card G.ConnectedComponent := by
    rw [Fintype.card_pos_iff]
    exact ⟨G.connectedComponentMk ⟨0, by omega⟩⟩
  refine ⟨G, hdec, hmin, hfree, ?_⟩
  norm_num at hmass
  omega

end Erdos85
