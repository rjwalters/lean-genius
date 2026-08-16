import Proofs.Erdos85FiniteEquivGluing
import Proofs.Erdos85OrderFortyNineT0NeighborhoodMatchings

namespace Erdos85

def sevenHighT0TargetN0 : Finset (Fin 49) :=
  Finset.univ.filter fun i => 7 ≤ i.val ∧ i.val < 15

def sevenHighT0TargetN1Only : Finset (Fin 49) :=
  Finset.univ.filter fun i => 15 ≤ i.val ∧ i.val < 22

def sevenHighT0TargetRest : Finset (Fin 49) :=
  Finset.univ.filter fun i => 22 ≤ i.val

theorem sevenHighT0TargetN0_card : sevenHighT0TargetN0.card = 8 := by
  native_decide

theorem sevenHighT0TargetN1Only_card : sevenHighT0TargetN1Only.card = 7 := by
  native_decide

theorem sevenHighT0TargetRest_card : sevenHighT0TargetRest.card = 27 := by
  native_decide

theorem sevenHighT0SourceN1Only_card :
    (sevenHighT0SupportFiber 1 \ sevenHighT0SupportFiber 0).card = 7 := by
  native_decide

theorem sevenHighT0SourceRest_card :
    (Finset.univ.filter fun i : Fin 49 =>
      7 ≤ i.val ∧
      i ∉ sevenHighT0SupportFiber 0 ∧
      i ∉ sevenHighT0SupportFiber 1).card = 27 := by
  native_decide

/-- Arithmetic coordinates on the target `N0 = {7,...,14}` block. -/
noncomputable def sevenHighT0TargetN0Coord :
    {i // i ∈ sevenHighT0TargetN0} ≃ Fin 8 :=
  Equiv.ofBijective
    (fun i => ⟨i.1.val - 7, by
      have hi := (Finset.mem_filter.mp i.2).2
      omega⟩)
    ⟨by
      intro i j h
      apply Subtype.ext
      apply Fin.ext
      have hi := (Finset.mem_filter.mp i.2).2
      have hj := (Finset.mem_filter.mp j.2).2
      have hh := congrArg Fin.val h
      simp at hh
      omega,
    by
      intro k
      refine ⟨⟨⟨k.val + 7, by omega⟩, ?_⟩, ?_⟩
      · simp [sevenHighT0TargetN0]
        omega
      · apply Fin.ext
        simp⟩

end Erdos85
