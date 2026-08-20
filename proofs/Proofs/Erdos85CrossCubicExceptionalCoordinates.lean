import Proofs.Erdos85MuNegThreeZeroFiveCorrectShoreGeometry

/-! # Exceptional coordinates for cross-shore cubic equality -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

def h305CrossCubicExceptionalCoordinates
    {V : Type*} [DecidableEq V]
    (u v : ZMod 8 → V) (i j : ZMod 8) : Finset V :=
  {u (i - 1), u (i + 1), v (j - 1), v (j + 1)}

set_option maxRecDepth 100000 in
private theorem zmodEight_plusMinus_ne :
    ∀ i : ZMod 8, i - 1 ≠ i + 1 := by
  native_decide

/-- The two coordinates adjacent to each endpoint on each C8 shore are four
distinct vertices. -/
theorem h305CrossCubicExceptionalCoordinates_card_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (u v : ZMod 8 → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hdisj : ∀ k l, u k ≠ v l) (i j : ZMod 8) :
    (h305CrossCubicExceptionalCoordinates u v i j).card = 4 := by
  classical
  have huu : u (i - 1) ≠ u (i + 1) :=
    huinj.ne (zmodEight_plusMinus_ne i)
  have hvv : v (j - 1) ≠ v (j + 1) :=
    hvinj.ne (zmodEight_plusMinus_ne j)
  simp [h305CrossCubicExceptionalCoordinates, huu, hvv,
    hdisj (i - 1) (j - 1), hdisj (i - 1) (j + 1),
    hdisj (i + 1) (j - 1), hdisj (i + 1) (j + 1)]

set_option maxRecDepth 100000 in
private theorem zmodEight_plusMinus_difference :
    ∀ i : ZMod 8, (i + 1) - (i - 1) = 2 := by
  native_decide

/-- In either correct h305 shore mode, the two exceptional coordinates on
one shore are not joined by an exterior edge (their cyclic offset is two). -/
theorem h305_crossExceptional_sameShore_not_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u : ZMod 8 → V)
    (hmode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (i : ZMod 8) :
    ¬ R.Adj (u (i - 1)) (u (i + 1)) := by
  rcases hmode with hmode | hmode
  · rw [hmode]
    rw [zmodEight_plusMinus_difference]
    native_decide
  · rw [hmode]
    rw [zmodEight_plusMinus_difference]
    native_decide

end

end Erdos85

#print axioms Erdos85.h305CrossCubicExceptionalCoordinates_card_four
#print axioms Erdos85.h305_crossExceptional_sameShore_not_adj
