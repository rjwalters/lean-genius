import Proofs.Erdos85FinalDyadicNegativeHighDefectLeakage

/-!
# Negative-high closure at saturated exceptional support

When the exceptional support has maximal size `c=q`, the full and empty
populations are forced.  The negative-high defect leakage then vanishes and
the induced defect degree on `M` is exactly `|E|-1`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- At `c=q`, the canonical empty and full populations are `2^j-r` and
`2^j+r`, respectively. -/
theorem finalDyadic_endpoint_full_empty_card_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q j r : ℕ} (hqa : q = 2 * 2 ^ j)
    (hreg : ∀ v, G.degree v = q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hrle : r ≤ 2 ^ j)
    (hsupport : (exceptionalSignedSupport G S q).card = q) :
    (emptyLineCenters G S).card = 2 ^ j - r ∧
      (fullLineCenters G S q).card = 2 ^ j + r := by
  let F := fullLineCenters G S q
  let E := emptyLineCenters G S
  have hsum := exceptionalSignedSupport_card_eq_full_add_empty
    G S (by rw [hqa]; positivity : 0 < q)
  rw [hsupport] at hsum
  change q = F.card + E.card at hsum
  have hdiff := finalDyadic_full_sub_empty_eq_cutDisplacement
    G hqa hreg S hdiv
  rw [hdisp] at hdiff
  change (F.card : ℤ) - E.card = 2 * r at hdiff
  have hsumZ : (q : ℤ) = (F.card : ℤ) + E.card := by exact_mod_cast hsum
  have hqaZ : (q : ℤ) = 2 * (2 ^ j : ℤ) := by exact_mod_cast hqa
  have hEint : (E.card : ℤ) = (2 ^ j : ℤ) - r := by omega
  have hFint : (F.card : ℤ) = (2 ^ j : ℤ) + r := by omega
  constructor
  · exact_mod_cast hEint
  · exact_mod_cast hFint

/-- At saturated support, every negative-high point has all its negative-shore
defect neighbors inside `M`, and its induced `M`-degree is exactly `|E|-1`. -/
theorem finalDyadic_negativeHigh_endpoint_defectClosure
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r : ℕ} (hq : 8 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j)
    (hsupport : (exceptionalSignedSupport G S q).card = q)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    {x : V} (hxM : x ∈ finalDyadicNegativeHighCutCenters G S j r) :
    ((secondOrderDefectGraph G).neighborFinset x ∩
        finalDyadicNegativeHighCutCenters G S j r).card =
      (emptyLineCenters G S).card - 1 ∧
    (((secondOrderDefectGraph G).neighborFinset x \ S) \
        finalDyadicNegativeHighCutCenters G S j r) = ∅ := by
  let D := secondOrderDefectGraph G
  let E := emptyLineCenters G S
  let M := finalDyadicNegativeHighCutCenters G S j r
  have hpop := finalDyadic_endpoint_full_empty_card_eq
    G hqa hreg S hdiv hdisp (by omega) hsupport
  have hinside :=
    finalDyadic_negativeHigh_inducedDefect_degree_ge_empty_sub_one
      G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
        hsupport hemptyClique hxM
  change E.card - 1 ≤ (D.neighborFinset x ∩ M).card at hinside
  have hMsub : M ⊆ Sᶜ := fun y hy => (Finset.mem_filter.mp hy).1
  have hsub : D.neighborFinset x ∩ M ⊆ D.neighborFinset x \ S := by
    intro y hy
    have hyData := Finset.mem_inter.mp hy
    exact Finset.mem_sdiff.mpr
      ⟨hyData.1, Finset.mem_compl.mp (hMsub hyData.2)⟩
  have hcut : (D.neighborFinset x ∩ S).card = 2 ^ j + r :=
    (Finset.mem_filter.mp hxM).2
  have hDcard : (D.neighborFinset x).card = q - 1 := by
    rw [D.card_neighborFinset_eq_degree,
      binarySquare_regular_secondOrderDefect_degree_eq
        G hfree (by omega) hreg hcard]
  have hout : (D.neighborFinset x \ S).card = 2 ^ j - 1 - r := by
    have hpartition := Finset.card_sdiff_add_card_inter
      (D.neighborFinset x) S
    rw [hDcard, hcut, hqa] at hpartition
    omega
  have hinsideUpper : (D.neighborFinset x ∩ M).card ≤
      2 ^ j - 1 - r := by
    rw [← hout]
    exact Finset.card_le_card hsub
  have hdegreeEq : (D.neighborFinset x ∩ M).card = E.card - 1 := by
    have hEpop := hpop.1
    change E.card = 2 ^ j - r at hEpop
    omega
  have hleak :=
    finalDyadic_negativeHigh_twice_defectLeakage_le_supportDeficit
      G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
        hsupport hemptyClique hxM
  change 2 * (((D.neighborFinset x \ S) \ M).card) ≤ q - q at hleak
  have hleakZero : ((D.neighborFinset x \ S) \ M).card = 0 := by omega
  exact ⟨hdegreeEq, Finset.card_eq_zero.mp hleakZero⟩

end

end Erdos85

#print axioms Erdos85.finalDyadic_endpoint_full_empty_card_eq
#print axioms Erdos85.finalDyadic_negativeHigh_endpoint_defectClosure
