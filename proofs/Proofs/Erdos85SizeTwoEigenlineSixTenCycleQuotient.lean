import Proofs.Erdos85SizeTwoEigenlineInternalCycleParity

/-!
# Exact defect quotient for the q=8 six-plus-ten cycle stratum

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

For internal cycle orders six and ten, the defect quotient has row sum seven,
is balanced with weights six and ten, and its six-cycle diagonal is at most
three.  These integer constraints determine the quotient uniquely.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- With rows ordered by cycle sizes six then ten, the internal defect
quotient is exactly `[[2,5],[3,4]]`. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_cycleQuotient
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
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10) :
    componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 2 ∧
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 5 ∧
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b a = 3 ∧
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b b = 4 := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  have hab : a ≠ b := by
    intro h
    rw [h] at ha
    omega
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
  change componentQuotientMatrix K H a a +
      componentQuotientMatrix K H a b = 7 at hrowA
  change componentQuotientMatrix K H b a +
      componentQuotientMatrix K H b b = 7 at hrowB
  change 6 * componentQuotientMatrix K H a b =
      10 * componentQuotientMatrix K H b a at hbal
  change componentQuotientMatrix K H a a ≤ 3 at hdiag
  have hQab_le : componentQuotientMatrix K H a b ≤ 7 := by omega
  have hQba_le : componentQuotientMatrix K H b a ≤ 7 := by omega
  have hoffdiag : componentQuotientMatrix K H a b = 5 ∧
      componentQuotientMatrix K H b a = 3 := by
    interval_cases hQab : componentQuotientMatrix K H a b <;>
      interval_cases hQba : componentQuotientMatrix K H b a <;> omega
  rcases hoffdiag with ⟨hAB, hBA⟩
  rw [hAB] at hrowA
  rw [hBA] at hrowB
  have hAA : componentQuotientMatrix K H a a = 2 := by omega
  have hBB : componentQuotientMatrix K H b b = 4 := by omega
  simpa [K, H] using And.intro hAA (And.intro hAB (And.intro hBA hBB))

end


end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_cycleQuotient
