import Proofs.Erdos85SizeTwoEigenlineInternalCycleParity

/-!
# Defect quotients for the q=8 eight-plus-eight cycle stratum

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

Equal cycle weights make the two-cycle defect quotient symmetric.  Its row
sum and the distance-two diagonal bound reduce the entire quotient to one
off-diagonal parameter in the interval `[2,7]`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- For two internal cycles of order eight, the defect quotient is
`[[7-r,r],[r,7-r]]` for an integer `2 ≤ r ≤ 7`. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_cycleQuotient
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 8) (hb : b.supp.ncard = 8) (hab : a ≠ b) :
    ∃ r : ℕ, 2 ≤ r ∧ r ≤ 7 ∧
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 7 - r ∧
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = r ∧
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b a = r ∧
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b b = 7 - r := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  have hcycle (d : H.ConnectedComponent) : 6 ≤ d.supp.ncard :=
    (binarySquare_regular_sizeTwoPart_internalCycle_even_six_le
      G hfree (by omega) hreg hcard c hc s hs_in hs_out hA_in d).2
  obtain ⟨hrows, hbalance, htotal⟩ :=
    binarySquare_regular_sizeTwoPart_cycleQuotient
      G hfree (by omega) hreg hcard c hc
  have hcardComp : Fintype.card H.ConnectedComponent ≤ 2 := by
    have hlower : 6 * Fintype.card H.ConnectedComponent ≤
        ∑ d : H.ConnectedComponent, d.supp.ncard := by
      calc
        6 * Fintype.card H.ConnectedComponent =
            ∑ _d : H.ConnectedComponent, 6 := by simp [Nat.mul_comm]
        _ ≤ ∑ d : H.ConnectedComponent, d.supp.ncard := by
          apply Finset.sum_le_sum
          intro d _
          exact hcycle d
    rw [htotal] at hlower
    omega
  have hcases (d : H.ConnectedComponent) : d = a ∨ d = b := by
    by_contra hd
    push Not at hd
    have hthree : 3 ≤ Fintype.card H.ConnectedComponent := by
      calc
        3 = ({a, b, d} : Finset H.ConnectedComponent).card := by
          simp [hab, hd.1.symm, hd.2.symm]
        _ ≤ (Finset.univ : Finset H.ConnectedComponent).card :=
          Finset.card_le_card (by simp)
        _ = Fintype.card H.ConnectedComponent := Finset.card_univ
    omega
  have huniv : (Finset.univ : Finset H.ConnectedComponent) = {a, b} := by
    ext d
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_iff]
    exact hcases d
  have hrowA := hrows a
  have hrowB := hrows b
  rw [huniv, Finset.sum_insert (by simpa using hab), Finset.sum_singleton] at hrowA
  rw [huniv, Finset.sum_insert (by simpa using hab), Finset.sum_singleton] at hrowB
  have hbal := hbalance a b
  rw [ha, hb] at hbal
  have hdiag := binarySquare_regular_sizeTwoPart_cycleQuotient_diagonal_le
    G hfree (by omega) hreg hcard c hc a (by omega)
  rw [ha] at hdiag
  let r := componentQuotientMatrix K H a b
  have hrSymm : componentQuotientMatrix K H b a = r := by
    change 8 * r = 8 * componentQuotientMatrix K H b a at hbal
    omega
  change componentQuotientMatrix K H a a + r = 7 at hrowA
  change componentQuotientMatrix K H b a +
      componentQuotientMatrix K H b b = 7 at hrowB
  change componentQuotientMatrix K H a a ≤ 5 at hdiag
  have hrLe : r ≤ 7 := by omega
  have htwoLe : 2 ≤ r := by omega
  have hAA : componentQuotientMatrix K H a a = 7 - r := by omega
  have hBB : componentQuotientMatrix K H b b = 7 - r := by omega
  refine ⟨r, htwoLe, hrLe, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [K, H, r] using hAA
  · simp [K, H, r]
  · simpa [K, H, r] using hrSymm
  · simpa [K, H, r] using hBB

end


end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_cycleQuotient
