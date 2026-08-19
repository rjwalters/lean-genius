import Proofs.Erdos85SizeTwoEigenlineSixTenCycleQuotient

/-!
# Internal-common cells in a C6+C10 component

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- On a cyclically labeled C10, two vertices have an internal common
neighbor exactly when their coordinate difference is `±2`. -/
theorem zmodTen_cycle_internalCommon_iff_offset_two_eight
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (v : ZMod 10 → V) (hvinj : Function.Injective v)
    (hv : ∀ z, H.neighborFinset (v z) = {v (z - 1), v (z + 1)}) :
    ∀ i j, i ≠ j → ((∃ z, H.Adj (v i) z ∧ H.Adj (v j) z) ↔
      j - i = 2 ∨ j - i = 8) := by
  have hadj : ∀ i z, H.Adj (v i) z ↔
      z = v (i - 1) ∨ z = v (i + 1) := by
    intro i z
    rw [← H.mem_neighborFinset, hv]
    simp
  intro i j hij
  constructor
  · rintro ⟨z, hiz, hjz⟩
    rcases (hadj i z).1 hiz with hz | hz <;>
      rcases (hadj j z).1 hjz with hz' | hz'
    · have h := hvinj (hz.symm.trans hz')
      exfalso
      apply hij
      linear_combination h
    · have := hvinj (hz.symm.trans hz')
      right
      have hneg : j - i = -2 := by
        calc
          j - i = (j + 1) - 1 - i := by ring
          _ = (i - 1) - 1 - i := by rw [this]
          _ = -2 := by ring
      calc
        j - i = -2 := hneg
        _ = 8 := by decide
    · have := hvinj (hz.symm.trans hz')
      left
      calc
        j - i = (j - 1) + 1 - i := by ring
        _ = (i + 1) + 1 - i := by rw [← this]
        _ = 2 := by ring
    · have := hvinj (hz.symm.trans hz')
      exfalso
      apply hij
      linear_combination this
  · intro h
    rcases h with h2 | h8
    · refine ⟨v (i + 1), (hadj i _).2 (Or.inr rfl), ?_⟩
      apply (hadj j _).2
      left
      apply congrArg v
      calc
        i + 1 = i + (j - i) - 1 := by rw [h2]; ring
        _ = j - 1 := by ring
    · refine ⟨v (i - 1), (hadj i _).2 (Or.inl rfl), ?_⟩
      apply (hadj j _).2
      right
      apply congrArg v
      have hneg : j - i = -2 := by
        calc
          j - i = 8 := h8
          _ = -2 := by decide
      calc
        i - 1 = i + (j - i) + 1 := by rw [hneg]; ring
        _ = j + 1 := by ring

/-- On a cyclically labeled C6, two vertices have an internal common
neighbor exactly when their coordinate difference is `±2`. -/
theorem zmodSix_cycle_internalCommon_iff_offset_two_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (u : ZMod 6 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)}) :
    ∀ i j, i ≠ j → ((∃ z, H.Adj (u i) z ∧ H.Adj (u j) z) ↔
      j - i = 2 ∨ j - i = 4) := by
  have hadj : ∀ i z, H.Adj (u i) z ↔
      z = u (i - 1) ∨ z = u (i + 1) := by
    intro i z
    rw [← H.mem_neighborFinset, hu]
    simp
  intro i j hij
  constructor
  · rintro ⟨z, hiz, hjz⟩
    rcases (hadj i z).1 hiz with hz | hz <;>
      rcases (hadj j z).1 hjz with hz' | hz'
    · have h := huinj (hz.symm.trans hz')
      exfalso
      apply hij
      linear_combination h
    · have := huinj (hz.symm.trans hz')
      right
      have hneg : j - i = -2 := by
        calc
          j - i = (j + 1) - 1 - i := by ring
          _ = (i - 1) - 1 - i := by rw [this]
          _ = -2 := by ring
      calc
        j - i = -2 := hneg
        _ = 4 := by decide
    · have := huinj (hz.symm.trans hz')
      left
      calc
        j - i = (j - 1) + 1 - i := by ring
        _ = (i + 1) + 1 - i := by rw [← this]
        _ = 2 := by ring
    · have := huinj (hz.symm.trans hz')
      exfalso
      apply hij
      linear_combination this
  · intro h
    rcases h with h2 | h4
    · refine ⟨u (i + 1), (hadj i _).2 (Or.inr rfl), ?_⟩
      apply (hadj j _).2
      left
      apply congrArg u
      calc
        i + 1 = i + (j - i) - 1 := by rw [h2]; ring
        _ = j - 1 := by ring
    · refine ⟨u (i - 1), (hadj i _).2 (Or.inl rfl), ?_⟩
      apply (hadj j _).2
      right
      apply congrArg u
      have hneg : j - i = -2 := by
        calc
          j - i = 4 := h4
          _ = -2 := by decide
      calc
        i - 1 = i + (j - i) + 1 := by rw [hneg]; ring
        _ = j + 1 := by ring

/-- Vertices on distinct connected cycles have no internal common neighbor. -/
theorem distinct_components_no_internalCommon
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (a b : H.ConnectedComponent) (hab : a ≠ b)
    {I J : Type*} (u : I → V) (v : J → V)
    (hua : ∀ i, H.connectedComponentMk (u i) = a)
    (hvb : ∀ j, H.connectedComponentMk (v j) = b) :
    ∀ i j, ¬ ∃ z, H.Adj (u i) z ∧ H.Adj (v j) z := by
  intro i j
  rintro ⟨z, hiz, hjz⟩
  have hi := ConnectedComponent.connectedComponentMk_eq_of_adj hiz
  have hj := ConnectedComponent.connectedComponentMk_eq_of_adj hjz
  apply hab
  exact (hua i).symm.trans (hi.trans (hj.symm.trans (hvb j)))

end

end Erdos85

#print axioms Erdos85.zmodTen_cycle_internalCommon_iff_offset_two_eight
#print axioms Erdos85.zmodSix_cycle_internalCommon_iff_offset_two_four
#print axioms Erdos85.distinct_components_no_internalCommon
