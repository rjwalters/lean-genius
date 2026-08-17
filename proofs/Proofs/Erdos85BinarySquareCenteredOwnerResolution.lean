import Proofs.Erdos85BinarySquareCenteredOwnerCross

/-!
# Resolution of the centered owner sectors

The centered owner Gram blocks resolve the nonconstant defect polynomial.
Together with pairwise annihilation, this makes each color an algebraic
summand of `q ((q-1)I-D)` and directly couples owner coordinates to the
cycle spectrum of the second-order defect graph.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The centered owner Gram blocks sum to the centered square-order defect
operator. -/
theorem binarySquare_regular_sum_centeredOwnerGrams
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 1 ≤ q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hsum : ∑ c, m c = q) :
    (∑ c : (secondOrderDefectGraph G).ConnectedComponent,
      ((q : ℤ) •
          ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ +
            (m c : ℤ) • (1 : Matrix V V ℤ)) -
        (m c : ℤ) • FriendshipTheoremOQ01.onesMatrix V)) =
      (q : ℤ) •
        (((q - 1 : ℕ) : ℤ) • (1 : Matrix V V ℤ) -
          (secondOrderDefectGraph G).adjMatrix ℤ) := by
  have hO :=
    sum_componentOwnerGraph_adjMatrix_eq_ones_sub_one_sub_secondOrderDefect
      G hfree
  have hsumZ : ∑ c, (m c : ℤ) = (q : ℤ) := by
    exact_mod_cast hsum
  rw [Finset.sum_sub_distrib]
  simp_rw [smul_add]
  rw [Finset.sum_add_distrib]
  rw [← Finset.smul_sum, hO]
  simp_rw [smul_smul]
  rw [← Finset.sum_smul, ← Finset.sum_smul]
  simp only [← Finset.mul_sum, hsumZ]
  simp only [FriendshipTheoremOQ01.onesMatrix]
  rw [Nat.cast_sub hq]
  module

/-- Pairwise annihilation turns every centered owner block into a summand of
the defect polynomial: multiplying by the full resolution selects precisely
that block. -/
theorem binarySquare_regular_centeredOwnerGram_mul_defectResolution
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = q * m c)
    (hsum : ∑ c, m c = q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    let C_c :=
      (q : ℤ) •
          ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ +
            (m c : ℤ) • (1 : Matrix V V ℤ)) -
        (m c : ℤ) • FriendshipTheoremOQ01.onesMatrix V
    C_c * ((q : ℤ) •
        (((q - 1 : ℕ) : ℤ) • (1 : Matrix V V ℤ) -
          (secondOrderDefectGraph G).adjMatrix ℤ)) = C_c * C_c := by
  dsimp
  let C : (secondOrderDefectGraph G).ConnectedComponent → Matrix V V ℤ :=
    fun d =>
      (q : ℤ) •
          ((componentOwnerGraph G (secondOrderDefectGraph G) d).adjMatrix ℤ +
            (m d : ℤ) • (1 : Matrix V V ℤ)) -
        (m d : ℤ) • FriendshipTheoremOQ01.onesMatrix V
  have hresolution : (∑ d, C d) =
      (q : ℤ) •
        (((q - 1 : ℕ) : ℤ) • (1 : Matrix V V ℤ) -
          (secondOrderDefectGraph G).adjMatrix ℤ) := by
    exact binarySquare_regular_sum_centeredOwnerGrams G hfree (by omega) m hsum
  rw [← hresolution]
  rw [Finset.mul_sum]
  apply Finset.sum_eq_single c
  · intro d _hd hdc
    exact binarySquare_regular_centeredOwnerGrams_mul_eq_zero
      G hfree hq hreg hcard c d hdc.symm (hm c) (hm d)
  · simp

end

end Erdos85
