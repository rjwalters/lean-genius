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

/-- Exact component partition of an order-eight two-regular graph: either a
single 8-cycle, or two cycles whose ordered sizes are `3+5`, `4+4`, or
`5+3`. -/
theorem twoRegular_orderEight_component_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : Fintype.card V = 8)
    (hdeg : ∀ x, H.degree x = 2) :
    (Fintype.card H.ConnectedComponent = 1 ∧
      ∀ c : H.ConnectedComponent, c.supp.ncard = 8) ∨
    (Fintype.card H.ConnectedComponent = 2 ∧
      ∀ c d : H.ConnectedComponent, c ≠ d →
        (c.supp.ncard = 3 ∧ d.supp.ncard = 5) ∨
        (c.supp.ncard = 4 ∧ d.supp.ncard = 4) ∨
        (c.supp.ncard = 5 ∧ d.supp.ncard = 3)) := by
  classical
  have hmin : ∀ c : H.ConnectedComponent, 3 ≤ c.supp.ncard := by
    intro c
    obtain ⟨r, hr, hre, _⟩ := twoRegular_component_charpoly_chebyshev H hdeg c
    simpa [hre] using hr
  have hsum : (∑ c : H.ConnectedComponent, c.supp.ncard) = 8 := by
    rw [sum_connectedComponent_supp_ncard H, hcard]
  have hcountLe : Fintype.card H.ConnectedComponent ≤ 2 := by
    have hthree : Fintype.card H.ConnectedComponent * 3 ≤
        ∑ c : H.ConnectedComponent, c.supp.ncard := by
      calc
        Fintype.card H.ConnectedComponent * 3 =
            ∑ _c : H.ConnectedComponent, 3 := by simp
        _ ≤ ∑ c : H.ConnectedComponent, c.supp.ncard :=
          Finset.sum_le_sum fun c _ ↦ hmin c
    omega
  have hcountPos : 0 < Fintype.card H.ConnectedComponent := by
    by_contra hnot
    have hzero : Fintype.card H.ConnectedComponent = 0 := by omega
    have huniv : (Finset.univ : Finset H.ConnectedComponent) = ∅ := by
      apply Finset.card_eq_zero.mp
      simpa using hzero
    rw [show (∑ c : H.ConnectedComponent, c.supp.ncard) =
        ∑ c ∈ (Finset.univ : Finset H.ConnectedComponent), c.supp.ncard by simp,
      huniv] at hsum
    simp at hsum
  rcases (show Fintype.card H.ConnectedComponent = 1 ∨
      Fintype.card H.ConnectedComponent = 2 by omega) with hcount | hcount
  · left
    refine ⟨hcount, ?_⟩
    intro c
    have hrestCard :
        ((Finset.univ : Finset H.ConnectedComponent).erase c).card = 0 := by
      simp [hcount]
    have hrest : (Finset.univ : Finset H.ConnectedComponent).erase c = ∅ :=
      Finset.card_eq_zero.mp hrestCard
    have hsplit := Finset.sum_erase_add
      (Finset.univ : Finset H.ConnectedComponent)
      (fun d ↦ d.supp.ncard) (Finset.mem_univ c)
    rw [hrest] at hsplit
    simp only [Finset.sum_empty, zero_add] at hsplit
    omega
  · right
    refine ⟨hcount, ?_⟩
    intro c d hcd
    have hrestCard :
        ((Finset.univ : Finset H.ConnectedComponent).erase c).card = 1 := by
      simp [hcount]
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hrestCard
    have hd : d ∈ (Finset.univ : Finset H.ConnectedComponent).erase c := by
      simp [hcd.symm]
    rw [ha] at hd
    have hda : d = a := by simpa using hd
    have had : a = d := hda.symm
    subst a
    have hsplit := Finset.sum_erase_add
      (Finset.univ : Finset H.ConnectedComponent)
      (fun e ↦ e.supp.ncard) (Finset.mem_univ c)
    rw [ha] at hsplit
    simp only [Finset.sum_singleton] at hsplit
    have hcCases := twoRegular_orderEight_component_size_cases H hcard hdeg c
    have hdCases := twoRegular_orderEight_component_size_cases H hcard hdeg d
    omega

end

end Erdos85

#print axioms Erdos85.twoRegular_orderEight_component_size_cases
#print axioms Erdos85.twoRegular_orderEight_component_partition
