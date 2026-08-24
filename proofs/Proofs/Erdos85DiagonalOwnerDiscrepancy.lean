import Mathlib

/-!
# Diagonal collapse of two-owner discrepancies

Scalar conservation over `ZMod 2` only says that the two owner coordinates
sum to zero.  For two Boolean owners this forces them to be equal, so the
entire unresolved contribution is a single coefficient multiplying the
diagonal class `(1,1)`.  This formalizes `(73rnz_cjibkzc)--(73rnz_cjibkzd)`
and also records why forgetting owner labels annihilates that class.
-/

namespace Erdos85

/-- The diagonal vector on the two Boolean owner labels. -/
def diagonalOwnerVector (delta : ZMod 2) : Bool → ZMod 2 :=
  fun _ => delta

/-- In characteristic two, two entries with zero sum are equal. -/
theorem f2_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  have hchar : (2 : ZMod 2) = 0 := by decide
  calc
    a = a + 0 := by rw [add_zero]
    _ = a + (a + b) := by rw [h]
    _ = (a + a) + b := by ac_rfl
    _ = 0 + b := by rw [← two_mul, hchar, zero_mul]
    _ = b := zero_add b

/-- Pointwise two-owner scalar conservation is exactly diagonality. -/
theorem ownerDiscrepancy_eq_of_scalarSum_zero
    {G : Type*} (delta : Bool → G → ZMod 2)
    (hzero : ∀ g, delta false g + delta true g = 0) :
    ∀ g, delta false g = delta true g := by
  intro g
  exact f2_eq_of_add_eq_zero (hzero g)

/-- **Diagonal owner collapse (`73rnz_cjibkzc--d`).**  If every residual
center has zero scalar discrepancy, then summing over any finite residual
block produces precisely one diagonal owner vector.  Its coefficient is
the sum of either owner coordinate. -/
theorem sum_ownerDiscrepancy_eq_diagonalOwnerVector
    {G : Type*} [DecidableEq G] (R : Finset G)
    (delta : Bool → G → ZMod 2)
    (hzero : ∀ g ∈ R, delta false g + delta true g = 0) :
    (fun owner => ∑ g ∈ R, delta owner g) =
      diagonalOwnerVector (∑ g ∈ R, delta false g) := by
  funext owner
  cases owner
  · rfl
  · simp only [diagonalOwnerVector]
    apply Finset.sum_congr rfl
    intro g hg
    exact (f2_eq_of_add_eq_zero (hzero g hg)).symm

/-- Forgetting owner labels kills every diagonal binary owner vector.  This
is why scalar conservation alone cannot determine its coefficient. -/
theorem sum_diagonalOwnerVector_eq_zero (delta : ZMod 2) :
    ∑ owner : Bool, diagonalOwnerVector delta owner = 0 := by
  have hchar : (2 : ZMod 2) = 0 := by decide
  rw [Fintype.sum_bool]
  change delta + delta = 0
  rw [← two_mul, hchar, zero_mul]

end Erdos85

#print axioms Erdos85.f2_eq_of_add_eq_zero
#print axioms Erdos85.ownerDiscrepancy_eq_of_scalarSum_zero
#print axioms Erdos85.sum_ownerDiscrepancy_eq_diagonalOwnerVector
#print axioms Erdos85.sum_diagonalOwnerVector_eq_zero
