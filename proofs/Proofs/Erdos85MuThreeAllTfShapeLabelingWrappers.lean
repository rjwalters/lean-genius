import Proofs.Erdos85MuThreeAllTfOrderSixtyFourWrappers
import Proofs.Erdos85MuThreeAllTfSixteenCoordinates
import Proofs.Erdos85MuThreeAllTfEightEightCoordinates

/-! # Component-size multisets supply all three all-TF shape labelings -/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem exists_sixteenCycleLabeling_of_componentSizes
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    [DecidableEq H.ConnectedComponent]
    (hdeg : ∀ x, H.degree x = 2)
    (hsizes : (↑[16] : Multiset ℕ) =
      (Finset.univ : Finset H.ConnectedComponent).val.map
        (fun c => c.supp.ncard)) :
    Nonempty (SixteenCycleLabeling H) := by
  classical
  obtain ⟨e, he⟩ := exists_equiv_fin_of_multiset_eq_map
    (fun c : H.ConnectedComponent => c.supp.ncard) [16] hsizes
  let a : H.ConnectedComponent := e 0
  have ha : a.supp.ncard = 16 := by
    simpa [a] using he (0 : Fin 1)
  have hcomponents : ∀ c : H.ConnectedComponent, c = a := by
    intro c
    let i : Fin 1 := e.symm c
    have hi : e i = c := e.apply_symm_apply c
    have hi0 : i = 0 := Fin.eq_zero i
    exact hi.symm.trans (by rw [hi0])
  have hspan : ∀ x : V, x ∈ a.supp := by
    intro x
    rw [ConnectedComponent.mem_supp_iff]
    exact hcomponents (H.connectedComponentMk x)
  exact exists_sixteenCycleLabeling_of_spanning_component
    H hdeg a ha hspan

theorem exists_eightEightCycleLabeling_of_componentSizes
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    [DecidableEq H.ConnectedComponent]
    (hdeg : ∀ x, H.degree x = 2)
    (hsizes : (↑[8, 8] : Multiset ℕ) =
      (Finset.univ : Finset H.ConnectedComponent).val.map
        (fun c => c.supp.ncard)) :
    Nonempty (EightEightCycleLabeling H) := by
  classical
  obtain ⟨e, he⟩ := exists_equiv_fin_of_multiset_eq_map
    (fun c : H.ConnectedComponent => c.supp.ncard) [8, 8] hsizes
  let a : H.ConnectedComponent := e 0
  let b : H.ConnectedComponent := e 1
  have ha : a.supp.ncard = 8 := by
    simpa [a] using he (0 : Fin 2)
  have hb : b.supp.ncard = 8 := by
    simpa [b] using he (1 : Fin 2)
  have hab : a ≠ b := by
    intro hab
    have h01 : (0 : Fin 2) = 1 := e.injective hab
    omega
  have hcomponents : ∀ c : H.ConnectedComponent, c = a ∨ c = b := by
    intro c
    let i : Fin 2 := e.symm c
    have hi : e i = c := e.apply_symm_apply c
    have hi01 : i = 0 ∨ i = 1 := by omega
    rcases hi01 with hi0 | hi1
    · left
      exact hi.symm.trans (by rw [hi0])
    · right
      exact hi.symm.trans (by rw [hi1])
  have hcover : ∀ x : V, x ∈ a.supp ∨ x ∈ b.supp := by
    intro x
    rcases hcomponents (H.connectedComponentMk x) with ha' | hb'
    · left
      simpa [ConnectedComponent.mem_supp_iff] using ha'
    · right
      simpa [ConnectedComponent.mem_supp_iff] using hb'
  exact exists_eightEightCycleLabeling_of_two_components
    H hdeg a b hab ha hb hcover

#print axioms exists_sixteenCycleLabeling_of_componentSizes
#print axioms exists_eightEightCycleLabeling_of_componentSizes

end

end Erdos85
