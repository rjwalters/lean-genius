import Proofs.Erdos85ThreeSeparatorFirstSliceWLocation

/-!
# Pole-wing concentration on the first non-endpoint slice

When the exceptional point `c` lies in the three-point separator, the
`c`-wing contains all but `m_c` of the `q - 2` residual-wing centers.
Equivalently, the other two wing colors contain exactly `m_c` centers and
hence at most four.  This is the numerical concentration statement in B30.
-/

open Finset

namespace Erdos85

noncomputable section

/-- Subtraction-free arithmetic core of B30.  Here `rc` is the size of the
residual wing at the exceptional pole and `off` is the total size of the
other two residual wings. -/
theorem poleWing_concentration_arithmetic
    (q m rc off : ℕ)
    (htotal : rc + off = q - 2)
    (hpole : rc + m = q - 2) :
    off = m := by
  omega

/-- If the pole attachment multiplicity is at most four, so is the entire
off-pole residual-wing mass. -/
theorem poleWing_offColor_le_four
    (q m rc off : ℕ)
    (htotal : rc + off = q - 2)
    (hpole : rc + m = q - 2)
    (hm : m ≤ 4) :
    off ≤ 4 := by
  rw [poleWing_concentration_arithmetic q m rc off htotal hpole]
  exact hm

/-- Finset form of B30.  If the residual-wing sizes over `W` total `q-2`
and the distinguished wing has size `q-2-m`, expressed without truncated
subtraction as `r c + m = q-2`, then the wings away from `c` have total
size exactly `m`. -/
theorem sum_residualWings_erase_exceptionalPole
    {V : Type*} [DecidableEq V]
    (W : Finset V) (c : V) (r : V → ℕ) (q m : ℕ)
    (hcW : c ∈ W)
    (htotal : ∑ w ∈ W, r w = q - 2)
    (hpole : r c + m = q - 2) :
    ∑ w ∈ W.erase c, r w = m := by
  have hsplit : (∑ w ∈ W.erase c, r w) + r c = q - 2 := by
    calc
      (∑ w ∈ W.erase c, r w) + r c = ∑ w ∈ W, r w :=
        Finset.sum_erase_add _ _ hcW
      _ = q - 2 := htotal
  omega

/-- The graph-facing bounded-perturbation conclusion of B30: at most four
residual-wing centers have a separator color different from `c`. -/
theorem sum_residualWings_erase_exceptionalPole_le_four
    {V : Type*} [DecidableEq V]
    (W : Finset V) (c : V) (r : V → ℕ) (q m : ℕ)
    (hcW : c ∈ W)
    (htotal : ∑ w ∈ W, r w = q - 2)
    (hpole : r c + m = q - 2)
    (hm : m ≤ 4) :
    ∑ w ∈ W.erase c, r w ≤ 4 := by
  rw [sum_residualWings_erase_exceptionalPole W c r q m hcW htotal hpole]
  exact hm

end

end Erdos85

#print axioms Erdos85.poleWing_concentration_arithmetic
#print axioms Erdos85.poleWing_offColor_le_four
#print axioms Erdos85.sum_residualWings_erase_exceptionalPole
#print axioms Erdos85.sum_residualWings_erase_exceptionalPole_le_four
