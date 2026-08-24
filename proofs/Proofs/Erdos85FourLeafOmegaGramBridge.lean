import Mathlib

/-!
# The four-leaf holonomy bit as a switch Gram defect

For an even residual-center switch degree `d`, the collision parity
`C(d,2)` equals the parity of `d/2`.  Summed over centers, the center-side
handshake identifies this with half the switch-edge census.  Substitution
into the four-leaf augmentation and row/column collision equations yields

`omega_Q = |N| + leafCollisions + Delta_J`.

This is the exact bridge `(73rnz_bk)` from the sole four-leaf pairing-gauge
class to the reversal-odd switch Gram ledger.
-/

namespace Erdos85

/-- For every even natural degree, `C(d,2)` and `d/2` have the same parity. -/
theorem cast_choose_two_eq_cast_half_of_even
    (d : ℕ) (hd : Even d) :
    ((Nat.choose d 2 : ℕ) : ZMod 2) = ((d / 2 : ℕ) : ZMod 2) := by
  obtain ⟨k, hk⟩ := hd
  subst d
  cases k with
  | zero => norm_num
  | succ k =>
      have hchoose :
          Nat.choose ((k + 1) + (k + 1)) 2 = (k + 1) * (2 * k + 1) := by
        rw [Nat.choose_two_right]
        have hsum : (k + 1) + (k + 1) = 2 * (k + 1) := by omega
        rw [hsum]
        have hpred : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
        rw [hpred]
        calc
          2 * (k + 1) * (2 * k + 1) / 2 =
              2 * ((k + 1) * (2 * k + 1)) / 2 := by ring_nf
          _ = (k + 1) * (2 * k + 1) := by
            exact Nat.mul_div_cancel_left ((k + 1) * (2 * k + 1))
              (by decide : 0 < 2)
      rw [hchoose]
      have hhalf : ((k + 1) + (k + 1)) / 2 = k + 1 := by omega
      rw [hhalf]
      push_cast
      have hchar : (2 : ZMod 2) = 0 := by decide
      rw [hchar, zero_mul, zero_add, mul_one]

/-- Centerwise even-degree collision parity, summed over any finite residual
center census. -/
theorem sum_cast_choose_two_eq_sum_cast_half_of_even
    {G : Type*} [DecidableEq G]
    (centers : Finset G) (degree : G → ℕ)
    (heven : ∀ g ∈ centers, Even (degree g)) :
    (∑ g ∈ centers, ((Nat.choose (degree g) 2 : ℕ) : ZMod 2)) =
      ∑ g ∈ centers, (((degree g) / 2 : ℕ) : ZMod 2) := by
  apply Finset.sum_congr rfl
  intro g hg
  exact cast_choose_two_eq_cast_half_of_even (degree g) (heven g hg)

/-- With the center-side half-handshake, the residual-center collision mass
is exactly half the switch-edge census in `F₂`. -/
theorem sum_centerCollision_eq_halfEdgeCount
    {G : Type*} [DecidableEq G]
    (centers : Finset G) (degree : G → ℕ) (edgeCount : ℕ)
    (heven : ∀ g ∈ centers, Even (degree g))
    (hhalfHandshake : ∑ g ∈ centers, degree g / 2 = edgeCount / 2) :
    (∑ g ∈ centers, ((Nat.choose (degree g) 2 : ℕ) : ZMod 2)) =
      (((edgeCount / 2 : ℕ)) : ZMod 2) := by
  rw [sum_cast_choose_two_eq_sum_cast_half_of_even centers degree heven]
  norm_cast
  exact congrArg (fun n : ℕ => (n : ZMod 2)) hhalfHandshake

private theorem f2_self_add (x : ZMod 2) : x + x = 0 := by
  have hchar : (2 : ZMod 2) = 0 := by decide
  rw [← two_mul, hchar, zero_mul]

/-- **Four-leaf omega/Gram bridge (`73rnz_bk`).**  `homega` is the
four-leaf augmentation formula and `hdelta` is the row-minus-column switch
collision defect.  In characteristic two their common center-collision term
eliminates, leaving the leaf-corrected Gram expression. -/
theorem fourLeafOmega_eq_cross_add_leafCollision_add_delta
    (omega crossCount leafCollision centerCollision deltaJ : ZMod 2)
    (homega : omega = crossCount + centerCollision)
    (hdelta : deltaJ = leafCollision + centerCollision) :
    omega = crossCount + leafCollision + deltaJ := by
  rw [homega, hdelta]
  calc
    crossCount + centerCollision =
        crossCount + leafCollision + (leafCollision + centerCollision) := by
      rw [add_assoc, ← add_assoc leafCollision leafCollision centerCollision,
        f2_self_add, zero_add]

end Erdos85

#print axioms Erdos85.cast_choose_two_eq_cast_half_of_even
#print axioms Erdos85.sum_centerCollision_eq_halfEdgeCount
#print axioms Erdos85.fourLeafOmega_eq_cross_add_leafCollision_add_delta
