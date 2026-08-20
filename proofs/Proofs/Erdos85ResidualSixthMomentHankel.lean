import Proofs.Erdos85RealRootPowerSums

/-! # Sixth-moment Hankel bound for the h305 residual -/

open Polynomial

namespace Erdos85

noncomputable section

/-- Multiplicity-aware Cauchy--Schwarz between the first and third powers
of the entries of a real multiset. -/
theorem multiset_fourth_sq_le_second_mul_sixth (s : Multiset ℝ) :
    (s.map fun x ↦ x ^ 4).sum ^ 2 ≤
      (s.map fun x ↦ x ^ 2).sum * (s.map fun x ↦ x ^ 6).sum := by
  let L := s.toList
  have h := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (Fin L.length))
    (fun i ↦ L[i]) (fun i ↦ L[i] ^ 3)
  rw [← Multiset.sum_map_toList, ← Multiset.sum_map_toList,
    ← Multiset.sum_map_toList]
  rw [← Fin.sum_univ_fun_getElem, ← Fin.sum_univ_fun_getElem,
    ← Fin.sum_univ_fun_getElem]
  have h13 (x : ℝ) : x * x ^ 3 = x ^ 4 := by ring
  have h33 (x : ℝ) : (x ^ 3) ^ 2 = x ^ 6 := by ring
  simpa [L, h13, h33] using h

/-- Real-root power sums satisfy the positive-semidefinite Hankel minor
`s₄² ≤ s₂ s₆`. -/
theorem realRootPowerSum_fourth_sq_le_second_mul_sixth (p : ℝ[X]) :
    realRootPowerSum p 4 ^ 2 ≤
      realRootPowerSum p 2 * realRootPowerSum p 6 := by
  exact multiset_fourth_sq_le_second_mul_sixth p.roots

/-- The h305 residual moments `s₂=224`, `s₄=1792` force
`s₆ ≥ 14336`. -/
theorem h305_realResidual_sixthMoment_lower
    (p : ℝ[X])
    (h2 : realRootPowerSum p 2 = 224)
    (h4 : realRootPowerSum p 4 = 1792) :
    14336 ≤ realRootPowerSum p 6 := by
  have h := realRootPowerSum_fourth_sq_le_second_mul_sixth p
  rw [h2, h4] at h
  nlinarith

end

end Erdos85

#print axioms Erdos85.multiset_fourth_sq_le_second_mul_sixth
#print axioms Erdos85.realRootPowerSum_fourth_sq_le_second_mul_sixth
#print axioms Erdos85.h305_realResidual_sixthMoment_lower
