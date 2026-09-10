import Proofs.Erdos85HoffmanDiagonalParity

/-! Diagonal power identities without an even-row-sum premise.
These supply the characteristic-two matrix step of weighted projector parity;
the quadratic-order/projector reduction is not formalized here. -/
namespace Erdos85
open Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem diagonal_even_power_mod_two (A : Matrix V V (ZMod 2))
    (hsymm : Aᵀ = A) (r : ℕ) (v : V) :
    (A ^ (2 * r)) v v = (A ^ r *ᵥ (fun _ => (1 : ZMod 2))) v := by
  have hpowT : (A ^ r)ᵀ = A ^ r := by rw [transpose_pow, hsymm]
  have hx (j : V) : (A ^ r) j v = (A ^ r) v j := by
    calc
      (A ^ r) j v = (A ^ r)ᵀ v j := rfl
      _ = (A ^ r) v j := by rw [hpowT]
  rw [two_mul, pow_add, mul_apply]
  simp only [hx, zmod2_mul_self]
  simp [mulVec, dotProduct]

theorem diagonal_odd_power_mod_two (A : Matrix V V (ZMod 2))
    (hsymm : Aᵀ = A) (hdiag : ∀ v, A v v = 0) (r : ℕ) (v : V) :
    (A ^ (2 * r + 1)) v v = 0 := by
  have hpowT : (A ^ r)ᵀ = A ^ r := by rw [transpose_pow, hsymm]
  have hx (j : V) : (A ^ r) j v = (A ^ r) v j := by
    calc
      (A ^ r) j v = (A ^ r)ᵀ v j := rfl
      _ = (A ^ r) v j := by rw [hpowT]
  have hsplit : 2 * r + 1 = r + (r + 1) := by omega
  rw [hsplit, pow_add, pow_succ', mul_apply]
  have hinner (i : V) :
      (A * A ^ r) i v = ∑ j, A i j * (A ^ r) v j := by
    rw [mul_apply]
    simp only [hx]
  simp only [hinner]
  have h := dotProduct_mulVec_self_eq_zero A hsymm hdiag (fun j => (A ^ r) v j)
  simpa [dotProduct, mulVec] using h

end Erdos85

#print axioms Erdos85.diagonal_even_power_mod_two
#print axioms Erdos85.diagonal_odd_power_mod_two
