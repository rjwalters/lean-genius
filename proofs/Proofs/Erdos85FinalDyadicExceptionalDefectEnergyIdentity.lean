import Proofs.Erdos85FinalDyadicExceptionalAdjacencyEnergy

/-!
# Exceptional adjacency energy through signed defect pairs

The square-order identity `A² = (q-1)I + J - D` evaluates the same quadratic
energy as the four-level cut census.  The remaining quadratic term is exactly
the signed defect incidence of the canonical full/empty support.
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- General quadratic form of the binary-square adjacency identity. -/
theorem binarySquare_adjEnergy_eq_mass_add_norm_sub_defectEnergy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ v, G.degree v = q) (z : V → ℤ) :
    ∑ v : V, ((G.adjMatrix ℤ).mulVec z v) ^ 2 =
      (∑ v : V, z v) ^ 2 + ((q : ℤ) - 1) * ∑ v : V, (z v) ^ 2 -
        ∑ v : V, z v *
          (∑ w ∈ (secondOrderDefectGraph G).neighborFinset v, z w) := by
  let A := G.adjMatrix ℤ
  let a := A.mulVec z
  have hsymm : A.transpose = A := G.isSymm_adjMatrix.eq
  have henergyDot : a ⬝ᵥ a = z ⬝ᵥ A.mulVec a := by
    calc
      a ⬝ᵥ a = (a ᵥ* A) ⬝ᵥ z := by
        change a ⬝ᵥ A.mulVec z = _
        rw [Matrix.dotProduct_mulVec]
      _ = A.mulVec a ⬝ᵥ z := by
        rw [← Matrix.vecMul_transpose, hsymm]
      _ = z ⬝ᵥ A.mulVec a := dotProduct_comm _ _
  calc
    ∑ v : V, (A.mulVec z v) ^ 2 = a ⬝ᵥ a := by
      simp [a, dotProduct, pow_two]
    _ = z ⬝ᵥ A.mulVec a := henergyDot
    _ = ∑ v : V, z v *
        (((q : ℤ) - 1) * z v + (∑ x : V, z x) -
          ∑ w ∈ (secondOrderDefectGraph G).neighborFinset v, z w) := by
      apply Finset.sum_congr rfl
      intro v _
      change z v * A.mulVec (A.mulVec z) v = _
      rw [Matrix.mulVec_mulVec]
      rw [binarySquare_regular_adjMatrix_sq_mulVec_apply G hfree hreg z v]
    _ = (∑ v : V, z v) ^ 2 + ((q : ℤ) - 1) *
          ∑ v : V, (z v) ^ 2 -
        ∑ v : V, z v *
          (∑ w ∈ (secondOrderDefectGraph G).neighborFinset v, z w) := by
      simp_rw [mul_sub, mul_add]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      have hfirst :
          (∑ v : V, z v * (((q : ℤ) - 1) * z v)) =
            ((q : ℤ) - 1) * ∑ v : V, (z v) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        ring
      have hmass :
          (∑ v : V, z v * (∑ x : V, z x)) = (∑ v : V, z v) ^ 2 := by
        rw [← Finset.sum_mul]
        ring
      rw [hfirst, hmass]
      ring

/-- Squaring the canonical exceptional sign gives the indicator of its
finite support. -/
theorem sum_sq_exceptionalOccupancySign_eq_support_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (q : ℕ) :
    ∑ v : V, (exceptionalOccupancySign G S q v) ^ 2 =
      ((exceptionalSignedSupport G S q).card : ℤ) := by
  have hpoint : ∀ v : V,
      (exceptionalOccupancySign G S q v) ^ 2 =
        if v ∈ exceptionalSignedSupport G S q then (1 : ℤ) else 0 := by
    intro v
    by_cases hf : (G.neighborFinset v ∩ S).card = q
    · simp [mem_exceptionalSignedSupport, exceptionalOccupancySign, hf]
    · by_cases he : (G.neighborFinset v ∩ S).card = 0
      · simp [mem_exceptionalSignedSupport, exceptionalOccupancySign, he]
      · simp [mem_exceptionalSignedSupport, exceptionalOccupancySign, hf, he]
  simp_rw [hpoint]
  have hnat := Finset.card_eq_sum_ite
    (s := exceptionalSignedSupport G S q) (t := Finset.univ)
    (Finset.subset_univ _)
  exact_mod_cast hnat.symm

/-- Final-dyadic specialization with support size `c` and displacement `2r`. -/
theorem finalDyadic_exceptionalAdjacencyEnergy_eq_defectEnergy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r c : ℕ}
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hsupport : (exceptionalSignedSupport G S q).card = c) :
    ∑ v : V, (finalDyadicExceptionalAdjacencyBalance G S q v) ^ 2 =
      (2 * (r : ℤ)) ^ 2 + ((q : ℤ) - 1) * c -
        ∑ v : V, exceptionalOccupancySign G S q v *
          (∑ w ∈ (secondOrderDefectGraph G).neighborFinset v,
            exceptionalOccupancySign G S q w) := by
  let z := exceptionalOccupancySign G S q
  have henergy := binarySquare_adjEnergy_eq_mass_add_norm_sub_defectEnergy
    G hfree hreg z
  have hsum := sum_exceptionalOccupancySign_eq_cutSign
    G (by rw [hqa]; positivity) hreg S
      (finalDyadic_occupancy_trichotomy G hqa hreg S hdiv)
  rw [hdisp] at hsum
  have hnorm := sum_sq_exceptionalOccupancySign_eq_support_card
    G S q
  rw [hsupport] at hnorm
  change ∑ v : V, ((G.adjMatrix ℤ).mulVec z v) ^ 2 = _ at henergy
  have hbalance : ∀ v,
      (G.adjMatrix ℤ).mulVec z v =
        finalDyadicExceptionalAdjacencyBalance G S q v := by
    intro v
    rw [SimpleGraph.adjMatrix_mulVec_apply]
    rfl
  simp_rw [hbalance] at henergy
  change (∑ v : V, z v) = 2 * r at hsum
  change (∑ v : V, (z v) ^ 2) = c at hnorm
  rw [hsum, hnorm] at henergy
  exact henergy

/-- Equating the pointwise four-level census with the binary-square energy
identity isolates the signed second-order defect contribution. -/
theorem finalDyadic_exceptionalCensus_eq_mass_norm_sub_defectEnergy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r c : ℕ} (hq : 3 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j)
    (hsupport : (exceptionalSignedSupport G S q).card = c) :
    (S.card : ℤ) +
        3 * (finalDyadicPositiveHighCutCenters G S q r).card +
        (finalDyadicNegativeHighCutCenters G S j r).card =
      (2 * (r : ℤ)) ^ 2 + ((q : ℤ) - 1) * c -
        ∑ v : V, exceptionalOccupancySign G S q v *
          (∑ w ∈ (secondOrderDefectGraph G).neighborFinset v,
            exceptionalOccupancySign G S q w) := by
  rw [← finalDyadic_exceptionalAdjacencyBalance_sum_sq
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf]
  exact finalDyadic_exceptionalAdjacencyEnergy_eq_defectEnergy
    G hfree hqa hreg S hdiv hdisp hsupport

end

end Erdos85

#print axioms
  Erdos85.binarySquare_adjEnergy_eq_mass_add_norm_sub_defectEnergy
#print axioms Erdos85.sum_sq_exceptionalOccupancySign_eq_support_card
#print axioms Erdos85.finalDyadic_exceptionalAdjacencyEnergy_eq_defectEnergy
#print axioms
  Erdos85.finalDyadic_exceptionalCensus_eq_mass_norm_sub_defectEnergy
