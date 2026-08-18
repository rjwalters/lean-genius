import Proofs.Erdos85BinarySquareCenteredOwnerBinaryTriangleDivisibility
import Proofs.Erdos85RegularGraphComplementTriangleLedger

/-!
# Mixed-owner triangle deficit in the binary square-order branch

Subtract the monochromatic owner triangles from all triangles in the
complement of the defect graph.  The cubic owner resolution and the regular
Goodman ledger force this signed deficit into an explicit congruence modulo
`6 * 2^(2k-1) = 3 * 2^(2k)`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Signed count of complement triangles not accounted for by monochromatic
component-owner triangles.  A later exact color-partition theorem can upgrade
the signed difference to a literal nonnegative mixed-color count. -/
def binarySquareMixedOwnerTriangleDeficit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent] : ℤ :=
  ((adjacencyTriangleMinorFinset (secondOrderDefectGraph G)ᶜ).card : ℤ) -
    ∑ c : (secondOrderDefectGraph G).ConnectedComponent,
      ((adjacencyTriangleMinorFinset
        (componentOwnerGraph G (secondOrderDefectGraph G) c)).card : ℤ)

/-- **Binary mixed-owner deficit congruence.**  The explicit Goodman
polynomial differs from six times the mixed-owner deficit by a multiple of
`6 * 2^(2k-1)`. -/
theorem binarySquare_regular_six_mul_two_pow_pred_dvd_goodman_sub_mixedOwnerDeficit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {k : ℕ} (hk : 2 ≤ k)
    (hreg : ∀ x, G.degree x = 2 ^ k)
    (hcard : Fintype.card V = (2 ^ k) * (2 ^ k))
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = (2 ^ k) * m c)
    (hsum : ∑ c, m c = 2 ^ k) :
    (6 * (2 : ℤ) ^ (2 * k - 1)) ∣
      (((2 ^ k) * (2 ^ k) : ℕ) : ℤ) *
          (((2 ^ k) * (2 ^ k) : ℕ) - 1) *
          (((2 ^ k) * (2 ^ k) : ℕ) - 2) -
        3 * (((2 ^ k) * (2 ^ k) : ℕ) : ℤ) *
          ((2 ^ k) - 1 : ℕ) *
          (((2 ^ k) * (2 ^ k) : ℕ) - 1 - ((2 ^ k) - 1 : ℕ)) -
        6 * binarySquareMixedOwnerTriangleDeficit G := by
  let D := secondOrderDefectGraph G
  let TD : ℤ := ((adjacencyTriangleMinorFinset D).card : ℤ)
  let TC : ℤ := ((adjacencyTriangleMinorFinset Dᶜ).card : ℤ)
  let SO : ℤ :=
    ∑ c : D.ConnectedComponent,
      ((adjacencyTriangleMinorFinset (componentOwnerGraph G D c)).card : ℤ)
  let p : ℤ := (2 : ℤ) ^ (2 * k - 1)
  let B : ℤ :=
    (((2 ^ k) * (2 ^ k) : ℕ) : ℤ) *
        (((2 ^ k) * (2 ^ k) : ℕ) - 1) *
        (((2 ^ k) * (2 ^ k) : ℕ) - 2) -
      3 * (((2 ^ k) * (2 ^ k) : ℕ) : ℤ) *
        ((2 ^ k) - 1 : ℕ) *
        (((2 ^ k) * (2 ^ k) : ℕ) - 1 - ((2 ^ k) - 1 : ℕ))
  have hq : 3 ≤ 2 ^ k := by
    have : 4 ≤ 2 ^ k := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  have hgood : 6 * (TD + TC) = B := by
    simpa [D, TD, TC, B] using
      (binarySquare_regular_defect_triangleMinorCount_add_compl
        G hfree hq hreg hcard)
  have howner : p ∣ TD + SO := by
    simpa [D, TD, SO, p] using
      (binarySquare_regular_two_pow_pred_dvd_sum_owner_defect_triangleMinorCounts
        G hfree hk hreg hcard m hm hsum)
  obtain ⟨z, hz⟩ := howner
  refine ⟨z, ?_⟩
  change B - 6 * (TC - SO) = (6 * p) * z
  calc
    B - 6 * (TC - SO) = 6 * (TD + SO) := by rw [← hgood]; ring
    _ = 6 * (p * z) := by rw [hz]
    _ = (6 * p) * z := by ring

end


end Erdos85

#print axioms
  Erdos85.binarySquare_regular_six_mul_two_pow_pred_dvd_goodman_sub_mixedOwnerDeficit
