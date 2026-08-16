import Proofs.Erdos85OrderFortyNineMatchingNormalization
import Proofs.Erdos85OrderFortyNineSevenHighProfileMasks

/-!
# Explicit support fibers for the seven-high empty triple system

The canonical `t = 0` mask array has eight low vertices over each high point,
and the fibers over highs zero and one meet in the unique pair-support vertex
numbered `7`.  These small facts are evaluated once here so the subsequent
normalization proof can remain structural.
-/

namespace Erdos85

open OrderFortyNineSevenHighCensus

def sevenHighT0Masks : Array Nat := representativeMasks 0 0

def sevenHighT0SupportFiber (w : Fin 7) : Finset (Fin 49) :=
  Finset.univ.filter fun i =>
    (orderFortyNineSupportMask sevenHighT0Masks i).getLsbD w.val

theorem sevenHighT0SupportFiber_card (w : Fin 7) :
    (sevenHighT0SupportFiber w).card = 8 := by
  native_decide +revert

theorem sevenHighT0SupportFiber_isLow
    (w : Fin 7) {x : Fin 49} (hx : x ∈ sevenHighT0SupportFiber w) :
    7 ≤ x.val := by
  native_decide +revert

theorem sevenHighT0SupportFiber_zero_one_inter :
    sevenHighT0SupportFiber 0 ∩ sevenHighT0SupportFiber 1 = {7} := by
  native_decide

@[simp] theorem sevenHighT0SupportFiber_zero_mem_seven :
    (7 : Fin 49) ∈ sevenHighT0SupportFiber 0 := by
  native_decide

@[simp] theorem sevenHighT0SupportFiber_one_mem_seven :
    (7 : Fin 49) ∈ sevenHighT0SupportFiber 1 := by
  native_decide

/-- A one-element filtered finite set supplies a unique subtype witness. -/
theorem existsUnique_subtype_of_filter_card_eq_one
    {P : Type*} [Fintype P] [DecidableEq P]
    (S : Finset P) (r : P → Bool)
    (hcard : (S.filter fun y => r y = true).card = 1) :
    ∃! y : {z // z ∈ S}, r y.1 = true := by
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hcard
  have hyMem : y ∈ S.filter (fun z => r z = true) := by simp [hy]
  refine ⟨⟨y, (Finset.mem_filter.mp hyMem).1⟩,
    (Finset.mem_filter.mp hyMem).2, ?_⟩
  intro z hz
  apply Subtype.ext
  have hzMem : z.1 ∈ S.filter (fun z => r z = true) :=
    Finset.mem_filter.mpr ⟨z.2, hz⟩
  simpa [hy] using hzMem

end Erdos85
