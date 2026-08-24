import Proofs.Erdos85FinalDyadicExceptionalFullDefectCapacity

/-!
# Population-free final exceptional capacity

The support population equations eliminate the auxiliary full/empty counts
from the defect-capacity squeeze, leaving a constraint only on the dyadic
parameters and the four-level cut census.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Integer form of the elementary identity `2 * choose(n,2) = n(n-1)`. -/
theorem two_mul_natChoose_two_cast (n : ℕ) :
    2 * (n.choose 2 : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
  have h : 2 * n.choose 2 = n * (n - 1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      cases n with
      | zero => simp
      | succ n =>
        simp [Nat.choose] at ih ⊢
        nlinarith
  have hnprod : (n : ℤ) * ((n : ℤ) - 1) = (n * (n - 1) : ℕ) := by
    by_cases hn : n = 0
    · simp [hn]
    · rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
  rw [hnprod]
  exact_mod_cast h

/-- Population-free arithmetic consequence of the final exceptional energy
and defect-regular capacity. -/
theorem finalDyadic_populationFree_exceptionalCensus_lower_bound
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
    (hsupport : (exceptionalSignedSupport G S q).card = c)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v) :
    (c : ℤ) ^ 2 + 2 * c * r + c - 2 * r +
        ((q : ℤ) - 1) * c - 2 * ((q : ℤ) - 1) * r ≤
      2 * ((S.card : ℤ) +
        3 * (finalDyadicPositiveHighCutCenters G S q r).card +
        (finalDyadicNegativeHighCutCenters G S j r).card) := by
  let F := fullLineCenters G S q
  let E := emptyLineCenters G S
  have hcap :=
    finalDyadic_exceptionalCensusResidual_add_full_empty_le_capacity
      G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf hsupport hemptyClique
  change _ + (F.card : ℤ) * E.card ≤
    ((q - 1 : ℕ) : ℤ) * F.card at hcap
  have hsumNat := exceptionalSignedSupport_card_eq_full_add_empty
    G S (by omega : 0 < q)
  rw [hsupport] at hsumNat
  change c = F.card + E.card at hsumNat
  have hsum : (F.card : ℤ) + E.card = c := by
    exact_mod_cast hsumNat.symm
  have hdiff := finalDyadic_full_sub_empty_eq_cutDisplacement
    G hqa hreg S hdiv
  rw [hdisp] at hdiff
  change (F.card : ℤ) - E.card = 2 * r at hdiff
  have hchoose := two_mul_natChoose_two_cast E.card
  have hqsub : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by
    omega
  rw [hqsub] at hcap
  nlinarith

/-- Eliminating the negative high class with the signed handshake turns the
population-free capacity into an explicit lower bound on `|P|`. -/
theorem finalDyadic_populationFree_positiveHighCutCenters_lower_bound
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
    (hsupport : (exceptionalSignedSupport G S q).card = c)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v) :
    (c : ℤ) ^ 2 + 2 * c * r + c - 2 * r +
        ((q : ℤ) - 1) * c - 2 * ((q : ℤ) - 1) * r +
        4 * (q : ℤ) * r - 4 * S.card ≤
      8 * (finalDyadicPositiveHighCutCenters G S q r).card := by
  have hlower := finalDyadic_populationFree_exceptionalCensus_lower_bound
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf hsupport hemptyClique
  have hdiff := finalDyadic_defectCutDegree_highClasses_card_sub
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
  nlinarith

/-- Since `P ⊆ S`, the preceding lower bound and the displacement equation
give a constraint purely on the arithmetic parameters `q,c,r`. -/
theorem finalDyadic_populationFree_parameter_capacity_bound
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
    (hsupport : (exceptionalSignedSupport G S q).card = c)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v) :
    (c : ℤ) ^ 2 + 2 * c * r + c - 2 * r +
        ((q : ℤ) - 1) * c - 2 * ((q : ℤ) - 1) * r +
        4 * (q : ℤ) * r ≤
      6 * (q : ℤ) ^ 2 + 12 * r := by
  have hP := finalDyadic_populationFree_positiveHighCutCenters_lower_bound
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf hsupport hemptyClique
  have hPsub : finalDyadicPositiveHighCutCenters G S q r ⊆ S := by
    exact Finset.filter_subset _ _
  have hPcardNat := Finset.card_le_card hPsub
  have hPcard :
      ((finalDyadicPositiveHighCutCenters G S q r).card : ℤ) ≤ S.card := by
    exact_mod_cast hPcardNat
  have hcardZ : (Fintype.card V : ℤ) = (q : ℤ) ^ 2 := by
    rw [hcard]
    push_cast
    ring
  rw [hcardZ] at hdisp
  nlinarith

end

end Erdos85

#print axioms Erdos85.two_mul_natChoose_two_cast
#print axioms
  Erdos85.finalDyadic_populationFree_exceptionalCensus_lower_bound
#print axioms
  Erdos85.finalDyadic_populationFree_positiveHighCutCenters_lower_bound
#print axioms
  Erdos85.finalDyadic_populationFree_parameter_capacity_bound
