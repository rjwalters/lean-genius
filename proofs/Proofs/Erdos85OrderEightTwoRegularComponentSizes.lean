import Proofs.Erdos85IsCyclesComponentCharpoly
import Proofs.Erdos85ResidueSignedCount

/-! # Component sizes of an order-eight two-regular graph -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Every connected component of a two-regular graph on eight vertices has
order `3`, `4`, `5`, or `8`.  Thus the full component partition is one of
`8`, `5+3`, or `4+4`. -/
theorem twoRegular_orderEight_component_size_cases
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : Fintype.card V = 8)
    (hdeg : ∀ x, H.degree x = 2)
    (c : H.ConnectedComponent) :
    c.supp.ncard = 3 ∨ c.supp.ncard = 4 ∨
      c.supp.ncard = 5 ∨ c.supp.ncard = 8 := by
  classical
  have hmin : ∀ d : H.ConnectedComponent, 3 ≤ d.supp.ncard := by
    intro d
    obtain ⟨r, hr, hre, _⟩ := twoRegular_component_charpoly_chebyshev H hdeg d
    simpa [hre] using hr
  have hsum : (∑ d : H.ConnectedComponent, d.supp.ncard) = 8 := by
    rw [sum_connectedComponent_supp_ncard H, hcard]
  have hle : c.supp.ncard ≤ 8 := by
    have := Finset.single_le_sum
      (s := (Finset.univ : Finset H.ConnectedComponent))
      (f := fun d ↦ d.supp.ncard)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ c)
    rw [hsum] at this
    simpa using this
  by_cases hc : c.supp.ncard = 8
  · exact Or.inr (Or.inr (Or.inr hc))
  have hlt : c.supp.ncard < 8 := lt_of_le_of_ne hle hc
  have hsplit := Finset.sum_erase_add
    (Finset.univ : Finset H.ConnectedComponent)
    (fun d ↦ d.supp.ncard) (Finset.mem_univ c)
  have hrest :
      (∑ d ∈ (Finset.univ : Finset H.ConnectedComponent).erase c,
        d.supp.ncard) + c.supp.ncard = 8 := by
    exact hsplit.trans hsum
  have hrestPos : 0 <
      ∑ d ∈ (Finset.univ : Finset H.ConnectedComponent).erase c,
        d.supp.ncard := by omega
  obtain ⟨d, hd, _hdpos⟩ :=
    (Finset.sum_pos_iff
      (s := (Finset.univ : Finset H.ConnectedComponent).erase c)
      (f := fun d ↦ d.supp.ncard)).mp hrestPos
  have hdle : d.supp.ncard ≤
      ∑ e ∈ (Finset.univ : Finset H.ConnectedComponent).erase c,
        e.supp.ncard := by
    exact Finset.single_le_sum
      (f := fun e : H.ConnectedComponent ↦ e.supp.ncard)
      (fun _ _ ↦ Nat.zero_le _) hd
  have hcmin := hmin c
  have hdmin := hmin d
  omega

end

end Erdos85

#print axioms Erdos85.twoRegular_orderEight_component_size_cases
