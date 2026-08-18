import Mathlib

/-! # Weighted reciprocal matrix obstruction modulo eight

The bipartite sign-vector basis is orthogonal but not normalized: its squared
norms are proportional to the defect-component parts.  Consequently the
integral adjacency coordinate matrix is weighted-symmetric rather than
symmetric.  This file isolates the algebra showing that involutivity of all
odd residues is still enough on the diagonal of its square.
-/

open Matrix

namespace Erdos85

/-- Every odd integer becomes an involution modulo eight. -/
theorem zmodEight_mul_self_eq_one_of_odd (x : ℤ) (hx : Odd x) :
    (x : ZMod 8) * (x : ZMod 8) = 1 := by
  obtain ⟨k, rfl⟩ := hx
  obtain ⟨t, ht | ht⟩ := Int.even_or_odd' k
  · rw [ht]
    push_cast
    ring_nf
    simp [show (8 : ZMod 8) = 0 by decide,
      show (16 : ZMod 8) = 0 by decide]
  · rw [ht]
    push_cast
    ring_nf
    rw [show (24 : ZMod 8) = 0 by decide,
      show (16 : ZMod 8) = 0 by decide,
      show (9 : ZMod 8) = 1 by decide]
    ring

/-- For a weighted-reciprocal matrix whose weights and entries square to one,
the diagonal scalar of `L²` equals each weight times the total weight.  Over
`ZMod 8`, the square-one hypotheses are automatic for odd integers. -/
theorem scalar_eq_weight_mul_sum_of_weighted_reciprocal_square
    {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (L : Matrix I I R) (m : I → R) (N : R)
    (hmSq : ∀ i, m i * m i = 1)
    (hLSq : ∀ i j, L i j * L i j = 1)
    (hrecip : ∀ i j, m j * L j i = m i * L i j)
    (hsq : L * L = N • (1 : Matrix I I R)) :
    ∀ i, N = m i * ∑ j, m j := by
  intro i
  have hterm : ∀ j, L i j * L j i = m i * m j := by
    intro j
    calc
      L i j * L j i = (m j * m j) * (L i j * L j i) := by rw [hmSq j, one_mul]
      _ = (m j * L i j) * (m j * L j i) := by ring
      _ = (m j * L i j) * (m i * L i j) := by rw [hrecip i j]
      _ = (m i * m j) * (L i j * L i j) := by ring
      _ = m i * m j := by rw [hLSq i j, mul_one]
  have hdiag := congrArg (fun M : Matrix I I R => M i i) hsq
  have hN : (L * L) i i = N := by
    rw [hdiag]
    simp
  calc
    N = (L * L) i i := hN.symm
    _ = ∑ j, L i j * L j i := by rw [Matrix.mul_apply]
    _ = ∑ j, m i * m j := by
      apply Finset.sum_congr rfl
      intro j _
      exact hterm j
    _ = m i * ∑ j, m j := by rw [Finset.mul_sum]

end Erdos85

#print axioms Erdos85.scalar_eq_weight_mul_sum_of_weighted_reciprocal_square
#print axioms Erdos85.zmodEight_mul_self_eq_one_of_odd
