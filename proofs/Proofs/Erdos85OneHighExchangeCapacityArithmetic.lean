import Proofs.Erdos85OneHighExchangedMissCounting

/-! # Eight-label exchange-capacity arithmetic -/

namespace Erdos85

noncomputable section

/-- An even natural number bounded by five is bounded by four. -/
theorem le_four_of_even_of_le_five {n : Nat} (heven : Even n) (hle : n ≤ 5) :
    n ≤ 4 := by
  rcases heven with ⟨k, hk⟩
  omega

/-- With eight labels, even incidence at every label and capacity five bound
the number of exchanged edges by sixteen. -/
theorem exchangeEdgeCount_le_sixteen_of_even_incidence_capacity_five
    (incidence : Fin 8 → Nat) (edgeCount : Nat)
    (heven : ∀ label, Even (incidence label))
    (hcapacity : ∀ label, incidence label ≤ 5)
    (hhandshake : (∑ label, incidence label) = 2 * edgeCount) :
    edgeCount ≤ 16 := by
  have hle : ∀ label, incidence label ≤ 4 := fun label =>
    le_four_of_even_of_le_five (heven label) (hcapacity label)
  have hsum : (∑ label, incidence label) ≤ ∑ _label : Fin 8, 4 :=
    Finset.sum_le_sum fun label _ => hle label
  norm_num at hsum
  omega

/-- Equality in the sixteen-edge bound saturates every label at incidence
four. -/
theorem incidence_eq_four_of_exchangeEdgeCount_eq_sixteen
    (incidence : Fin 8 → Nat)
    (heven : ∀ label, Even (incidence label))
    (hcapacity : ∀ label, incidence label ≤ 5)
    (hhandshake : (∑ label, incidence label) = 2 * 16) :
    ∀ label, incidence label = 4 := by
  have hle : ∀ label, incidence label ≤ 4 := fun label =>
    le_four_of_even_of_le_five (heven label) (hcapacity label)
  intro label
  have hrest :
      (∑ x ∈ (Finset.univ : Finset (Fin 8)).erase label, incidence x) ≤
        ∑ _x ∈ (Finset.univ : Finset (Fin 8)).erase label, 4 :=
    Finset.sum_le_sum fun x _ => hle x
  have hcard : ((Finset.univ : Finset (Fin 8)).erase label).card = 7 := by
    simp
  simp only [Finset.sum_const, nsmul_eq_mul, hcard] at hrest
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin 8))
    incidence (Finset.mem_univ label)
  rw [hhandshake] at hsplit
  have hge : 4 ≤ incidence label := by omega
  exact Nat.le_antisymm (hle label) hge

end

end Erdos85
