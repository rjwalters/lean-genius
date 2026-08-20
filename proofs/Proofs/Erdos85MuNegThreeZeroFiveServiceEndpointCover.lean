import Proofs.Erdos85EdgeIndexedServiceEndpointCover
import Proofs.Erdos85MuNegThreeZeroFiveServiceStarMatching

/-! # Coordinate endpoint cover for an h305 service star -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- The coordinate support predicted for the six service neighbors of an
exterior edge whose endpoints lie on the `u` shore. -/
def h305ServiceCoordinateCover
    {V : Type*} [Fintype V] [DecidableEq V]
    (u v : ZMod 8 → V) (i j : ZMod 8) : Finset V :=
  (h305ServiceEligibleCoordinates i j).image u ∪ Finset.univ.image v

/-- For two disjoint labeled eight-cycle shores, the endpoint cover of a
same-shore service star is precisely the four eligible vertices on that shore
together with the entire opposite shore. -/
theorem h305_serviceNeighborEndpointCover_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (u v : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hdisj : ∀ k l, u k ≠ v l)
    (hcover : ∀ x : V, (∃ k, x = u k) ∨ ∃ l, x = v l)
    (a : R.edgeFinset) (i j : ZMod 8)
    (ha : a.1.toFinset = {u i, u j}) :
    serviceNeighborEndpointCover R Cedge a =
      h305ServiceCoordinateCover u v i j := by
  classical
  rw [edgeIndexedService_neighborEndpointCover_eq H R Cedge hservice a]
  ext x
  rcases hcover x with ⟨k, rfl⟩ | ⟨l, rfl⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      h305ServiceCoordinateCover, Finset.mem_union, Finset.mem_image]
    constructor
    · intro hz
      left
      refine ⟨k, ?_, rfl⟩
      simp only [h305ServiceEligibleCoordinates, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [Finset.card_eq_zero] at hz
      have noAdj (z : ZMod 8) (hzmem : z = k - 1 ∨ z = k + 1) :
          u z ∉ a.1.toFinset := by
        intro hmem
        have hadj : H.Adj (u k) (u z) := by
          apply (H.mem_neighborFinset (u k) (u z)).mp
          rw [hu k]
          rcases hzmem with rfl | rfl <;> simp
        have : u z ∈ internalEndpointNeighborFinset H R (u k) a :=
          Finset.mem_filter.mpr ⟨hmem, hadj⟩
        simpa [hz] using this
      rw [ha] at noAdj
      constructor
      · intro hik
        exact noAdj i (Or.inl hik) (by simp)
      constructor
      · intro hik
        exact noAdj i (Or.inr hik) (by simp)
      constructor
      · intro hjk
        exact noAdj j (Or.inl hjk) (by simp)
      · intro hjk
        exact noAdj j (Or.inr hjk) (by simp)
    · intro htarget
      rcases htarget with hsame | hopp
      · rcases hsame with ⟨q, hq, hqu⟩
        have hk' : k ∈ h305ServiceEligibleCoordinates i j := by
          exact huinj hqu ▸ hq
        rw [Finset.card_eq_zero]
        ext y
        simp only [internalEndpointNeighborFinset, Finset.mem_filter,
          Finset.notMem_empty, iff_false, not_and]
        intro hya
        rw [ha] at hya
        simp only [Finset.mem_insert, Finset.mem_singleton] at hya
        rcases hya with hyi | hyj
        · subst y
          intro hadj
          have hm := (H.mem_neighborFinset (u k) (u i)).mpr hadj
          rw [hu k] at hm
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with hpred | hsucc
          · exact (Finset.mem_filter.mp hk').2.1 (huinj hpred)
          · exact (Finset.mem_filter.mp hk').2.2.1 (huinj hsucc)
        · subst y
          intro hadj
          have hm := (H.mem_neighborFinset (u k) (u j)).mpr hadj
          rw [hu k] at hm
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with hpred | hsucc
          · exact (Finset.mem_filter.mp hk').2.2.2.1 (huinj hpred)
          · exact (Finset.mem_filter.mp hk').2.2.2.2 (huinj hsucc)
      · rcases hopp with ⟨q, hq⟩
        exact (hdisj k q hq.symm).elim
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      h305ServiceCoordinateCover, Finset.mem_union, Finset.mem_image]
    constructor
    · intro _
      exact Or.inr ⟨l, rfl⟩
    · intro _
      rw [Finset.card_eq_zero]
      ext y
      simp only [internalEndpointNeighborFinset, Finset.mem_filter,
        Finset.notMem_empty, iff_false, not_and]
      intro hya
      rw [ha] at hya
      simp only [Finset.mem_insert, Finset.mem_singleton] at hya
      rcases hya with hyi | hyj
      · subst y
        intro hadj
        have hm := (H.mem_neighborFinset (u i) (v l)).mpr hadj.symm
        rw [hu i] at hm
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with hpred | hsucc
        · exact hdisj (i - 1) l hpred.symm
        · exact hdisj (i + 1) l hsucc.symm
      · subst y
        intro hadj
        have hm := (H.mem_neighborFinset (u j) (v l)).mpr hadj.symm
        rw [hu j] at hm
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with hpred | hsucc
        · exact hdisj (j - 1) l hpred.symm
        · exact hdisj (j + 1) l hsucc.symm

/-- In each corrected h305 within-shore mode, the six neighboring service
edges cover exactly twelve vertices: four on the central shore and eight on
the opposite shore. -/
theorem h305_serviceNeighborEndpointCover_card_twelve
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (u v : ZMod 8 → V) (huinj : Function.Injective u)
    (hvinj : Function.Injective v)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hdisj : ∀ k l, u k ≠ v l)
    (hcover : ∀ x : V, (∃ k, x = u k) ∨ ∃ l, x = v l)
    (a : R.edgeFinset) (i j : ZMod 8)
    (ha : a.1.toFinset = {u i, u j})
    (hoffset : j - i = 1 ∨ j - i = 3 ∨ j - i = 4 ∨
      j - i = 5 ∨ j - i = 7) :
    (serviceNeighborEndpointCover R Cedge a).card = 12 := by
  classical
  rw [h305_serviceNeighborEndpointCover_eq H R Cedge hservice u v huinj hu
    hdisj hcover a i j ha]
  unfold h305ServiceCoordinateCover
  have hd : Disjoint
      ((h305ServiceEligibleCoordinates i j).image u)
      (Finset.univ.image v) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    rcases Finset.mem_image.mp hx with ⟨k, -, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨l, -, hlu⟩
    exact hdisj k l hlu.symm
  rw [Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ huinj,
    Finset.card_image_of_injective _ hvinj,
    h305ServiceEligibleCoordinates_card_four i j hoffset]
  decide

end

end Erdos85

#print axioms Erdos85.h305_serviceNeighborEndpointCover_eq
#print axioms Erdos85.h305_serviceNeighborEndpointCover_card_twelve
