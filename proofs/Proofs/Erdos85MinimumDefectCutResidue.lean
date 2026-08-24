import Proofs.Erdos85DefectMaxEdgeConnectivity
import Proofs.Erdos85ClosedNeighborhoodCutTriangleIdentity
import Proofs.Erdos85EulerianCutParity

/-!
# Residues of minimum second-order defect cuts

At square order, the sharp regular-cut lower bound says that a cut of size
`q - 1` can only have shore residue `0`, `1`, or `-1` modulo `q`.  For the
second-order defect graph in the binary branch, parity excludes residue zero:
the graph has odd degree `q - 1`, its minimum cut is odd, and hence its shore
has odd cardinality, whereas a multiple of the even number `q` is even.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The only residues whose regular-square cut lower bound is at most `q-1`
are `0`, `1`, and `q-1`. -/
theorem mod_eq_zero_or_one_or_pred_of_regularSquareCutLower_le_pred
    (q s : ℕ) (hq : 4 ≤ q)
    (hlower : regularSquareCutLower q s ≤ ((q - 1 : ℕ) : ℤ)) :
    s % q = 0 ∨ s % q = 1 ∨ s % q = q - 1 := by
  have hqpos : 0 < q := by omega
  rw [regularSquareCutLower_eq_mod_product q s hqpos] at hlower
  have hprod : (s % q) * (q - s % q) ≤ q - 1 := by
    exact_mod_cast hlower
  have hrlt : s % q < q := Nat.mod_lt _ hqpos
  by_cases hr0 : s % q = 0
  · exact Or.inl hr0
  by_cases hr1 : s % q = 1
  · exact Or.inr (Or.inl hr1)
  by_cases hrpred : s % q = q - 1
  · exact Or.inr (Or.inr hrpred)
  exfalso
  have hrlo : 2 ≤ s % q := by omega
  have hrhi : s % q ≤ q - 2 := by omega
  have hq2 : 2 ≤ q := by omega
  have hqr : s % q ≤ q := by omega
  have hprodZ : ((s % q : ℕ) : ℤ) *
      ((q : ℤ) - (s % q : ℕ)) ≤ (q : ℤ) - 1 := by
    calc
      ((s % q : ℕ) : ℤ) * ((q : ℤ) - (s % q : ℕ)) =
          (((s % q) * (q - s % q) : ℕ) : ℤ) := by
            rw [Nat.cast_mul, Nat.cast_sub hqr]
      _ ≤ ((q - 1 : ℕ) : ℤ) := by exact_mod_cast hprod
      _ = (q : ℤ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ q)]; norm_num
  have hleft : 0 ≤ ((s % q : ℕ) : ℤ) - 2 := by
    exact sub_nonneg.mpr (by exact_mod_cast hrlo)
  have hright : 0 ≤ ((q : ℤ) - (s % q : ℕ)) - 2 := by
    have hrightNat : 2 ≤ q - s % q := by omega
    have hrightCast : (2 : ℤ) ≤ ((q - s % q : ℕ) : ℤ) := by
      exact_mod_cast hrightNat
    rw [Nat.cast_sub hqr] at hrightCast
    exact sub_nonneg.mpr hrightCast
  have hnonneg :
      0 ≤ (((s % q : ℕ) : ℤ) - 2) *
        (((q : ℤ) - (s % q : ℕ)) - 2) := by
    exact mul_nonneg hleft hright
  have hrloZ : (2 : ℤ) ≤ (s % q : ℕ) := by exact_mod_cast hrlo
  have hrhiZ : ((s % q : ℕ) : ℤ) ≤ (q : ℤ) - 2 := by
    exact_mod_cast hrhi
  have hqZ : (4 : ℤ) ≤ q := by exact_mod_cast hq
  nlinarith [hnonneg]

/-- In an odd-regular graph, an odd cut has an odd-cardinality shore. -/
theorem odd_card_of_regular_odd_cut
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] {r : ℕ}
    (hreg : ∀ x, D.degree x = r)
    (S : Finset V) (hcutOdd : Odd (finsetGraphCutSize D S)) :
    Odd S.card := by
  have hdegree :=
    finsetGraphCutSize_add_sum_internal_eq_card_mul_of_regular D hreg S
  have hinternal := even_sum_internalNeighbor_card D S
  have hproductOdd : Odd (S.card * r) := by
    rw [← hdegree]
    exact hcutOdd.add_even hinternal
  rcases Nat.even_or_odd S.card with hcardEven | hcardOdd
  · have hproductEven : Even (S.card * r) := hcardEven.mul_right r
    obtain ⟨a, ha⟩ := hproductOdd
    obtain ⟨b, hb⟩ := hproductEven
    omega
  · exact hcardOdd

/-- A cut of the minimum possible positive size `q-1` in the second-order
defect graph has shore size congruent to `+1` or `-1` modulo `q`. -/
theorem binarySquare_pred_defectCut_card_mod_eq_one_or_pred
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 4 ≤ q)
    (hqEven : Even q) (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hcut : finsetGraphCutSize (secondOrderDefectGraph G) S = q - 1) :
    S.card % q = 1 ∨ S.card % q = q - 1 := by
  let D := secondOrderDefectGraph G
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDreg : ∀ v, D.degree v = q - 1 := by
    intro v
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus v
    change D.degree v = (q - 3) + 2 at h
    omega
  have hlower := c4Free_regularSquareCutLower_le_defectCut
    G hfree (by omega : 1 ≤ q) hreg hcard S
  rw [hcut] at hlower
  obtain hzero | hone | hpred :=
    mod_eq_zero_or_one_or_pred_of_regularSquareCutLower_le_pred
      q S.card hq hlower
  · exfalso
    have hqOddPred : Odd (q - 1) := by
      obtain ⟨a, ha⟩ := hqEven
      use a - 1
      omega
    have hcardOdd : Odd S.card := by
      apply odd_card_of_regular_odd_cut D hDreg S
      rw [hcut]
      exact hqOddPred
    have hqdvd : q ∣ S.card := by
      rw [Nat.dvd_iff_mod_eq_zero]
      exact hzero
    obtain ⟨b, hb⟩ := hqdvd
    have hcardEven : Even S.card := by
      rw [hb]
      exact hqEven.mul_right b
    obtain ⟨a, ha⟩ := hcardEven
    obtain ⟨c, hc⟩ := hcardOdd
    omega
  · exact Or.inl hone
  · exact Or.inr hpred

end

end Erdos85

#print axioms Erdos85.mod_eq_zero_or_one_or_pred_of_regularSquareCutLower_le_pred
#print axioms Erdos85.odd_card_of_regular_odd_cut
#print axioms Erdos85.binarySquare_pred_defectCut_card_mod_eq_one_or_pred
