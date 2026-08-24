import Proofs.Erdos85FinalDyadicDefectCutDegreeQuantization

/-!
# Census of the two final-dyadic defect-cut degree classes

The two possible cut degrees on each shore define canonical high classes.
Counting the same defect cut from both shores gives an exact population
difference between those classes.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

def finalDyadicPositiveHighCutCenters
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (q r : ℕ) : Finset V :=
  S.filter fun v =>
    ((secondOrderDefectGraph G).neighborFinset v \ S).card = q - r

def finalDyadicNegativeHighCutCenters
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (j r : ℕ) : Finset V :=
  Sᶜ.filter fun v =>
    ((secondOrderDefectGraph G).neighborFinset v ∩ S).card = 2 ^ j + r

/-- Exact fraction-free handshake between the two high cut-degree classes. -/
theorem finalDyadic_defectCutDegree_highClasses_handshake
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r : ℕ} (hq : 3 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j) :
    S.card * (2 ^ j - r) +
        2 ^ j * (finalDyadicPositiveHighCutCenters G S q r).card =
      (Sᶜ : Finset V).card * r +
        2 ^ j * (finalDyadicNegativeHighCutCenters G S j r).card := by
  let D := secondOrderDefectGraph G
  let P := finalDyadicPositiveHighCutCenters G S q r
  let M := finalDyadicNegativeHighCutCenters G S j r
  have hpos : ∀ v ∈ S,
      (D.neighborFinset v \ S).card =
        (2 ^ j - r) + if v ∈ P then 2 ^ j else 0 := by
    intro v hv
    have htwo := finalDyadic_positiveShore_defectCutDegree_twoLevel
      G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf v hv
    by_cases hvP : v ∈ P
    · have hhigh : (D.neighborFinset v \ S).card = q - r :=
        (Finset.mem_filter.mp hvP).2
      rw [if_pos hvP, hhigh, hqa]
      omega
    · have hnotHigh : (D.neighborFinset v \ S).card ≠ q - r := by
        intro hh
        exact hvP (Finset.mem_filter.mpr ⟨hv, hh⟩)
      have hlow : (D.neighborFinset v \ S).card = 2 ^ j - r :=
        htwo.resolve_right hnotHigh
      simp [hvP, hlow]
  have hneg : ∀ v ∈ (Sᶜ : Finset V),
      (D.neighborFinset v ∩ S).card =
        r + if v ∈ M then 2 ^ j else 0 := by
    intro v hv
    have hvNot : v ∉ S := Finset.mem_compl.mp hv
    have htwo := finalDyadic_negativeShore_defectCutDegree_twoLevel
      G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf v hvNot
    by_cases hvM : v ∈ M
    · have hhigh : (D.neighborFinset v ∩ S).card = 2 ^ j + r :=
        (Finset.mem_filter.mp hvM).2
      rw [if_pos hvM, hhigh]
      omega
    · have hnotHigh : (D.neighborFinset v ∩ S).card ≠ 2 ^ j + r := by
        intro hh
        exact hvM (Finset.mem_filter.mpr ⟨hv, hh⟩)
      have hlow : (D.neighborFinset v ∩ S).card = r :=
        htwo.resolve_right hnotHigh
      simp [hvM, hlow]
  have hswap := sum_card_neighbor_inter_comm D S (Sᶜ : Finset V)
  have hleft :
      ∑ v ∈ S, (D.neighborFinset v ∩ (Sᶜ : Finset V)).card =
        S.card * (2 ^ j - r) + 2 ^ j * P.card := by
    calc
      _ = ∑ v ∈ S, ((2 ^ j - r) + if v ∈ P then 2 ^ j else 0) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [show D.neighborFinset v ∩ (Sᶜ : Finset V) =
            D.neighborFinset v \ S by ext x; simp]
        exact hpos v hv
      _ = S.card * (2 ^ j - r) + 2 ^ j * P.card := by
        rw [Finset.sum_add_distrib]
        rw [Finset.sum_ite_mem]
        have hPS : S ∩ P = P := by
          apply Finset.inter_eq_right.mpr
          intro x hx
          exact (Finset.mem_filter.mp hx).1
        rw [hPS]
        simp [Nat.mul_comm]
  have hright :
      ∑ v ∈ (Sᶜ : Finset V), (D.neighborFinset v ∩ S).card =
        (Sᶜ : Finset V).card * r + 2 ^ j * M.card := by
    calc
      _ = ∑ v ∈ (Sᶜ : Finset V),
          (r + if v ∈ M then 2 ^ j else 0) := by
        apply Finset.sum_congr rfl
        exact hneg
      _ = (Sᶜ : Finset V).card * r + 2 ^ j * M.card := by
        rw [Finset.sum_add_distrib]
        rw [Finset.sum_ite_mem]
        have hMS : (Sᶜ : Finset V) ∩ M = M := by
          apply Finset.inter_eq_right.mpr
          intro x hx
          exact (Finset.mem_filter.mp hx).1
        rw [hMS]
        simp [Nat.mul_comm]
  change S.card * (2 ^ j - r) + 2 ^ j * P.card =
    (Sᶜ : Finset V).card * r + 2 ^ j * M.card
  rw [← hleft, ← hright]
  exact hswap

/-- Solving the handshake gives the exact signed population difference of
the two high classes. -/
theorem finalDyadic_defectCutDegree_highClasses_card_sub
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r : ℕ} (hq : 3 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j) :
    ((finalDyadicPositiveHighCutCenters G S q r).card : ℤ) -
        (finalDyadicNegativeHighCutCenters G S j r).card =
      2 * (q : ℤ) * r - S.card := by
  have hhand := finalDyadic_defectCutDegree_highClasses_handshake
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
  have hsplit : (Sᶜ : Finset V).card + S.card = q * q := by
    rw [Finset.card_compl_add_card, hcard]
  have hhpos : 0 < 2 ^ j := by positivity
  have hqaZ : (q : ℤ) = 2 * (2 ^ j : ℕ) := by exact_mod_cast hqa
  have hsplitZ : ((Sᶜ : Finset V).card : ℤ) + S.card = q * q := by
    exact_mod_cast hsplit
  have hhandZ :
      (S.card : ℤ) * (((2 ^ j : ℕ) - r : ℕ) : ℤ) +
          ((2 ^ j : ℕ) : ℤ) *
            ((finalDyadicPositiveHighCutCenters G S q r).card : ℤ) =
        ((Sᶜ : Finset V).card : ℤ) * (r : ℤ) +
          ((2 ^ j : ℕ) : ℤ) *
            ((finalDyadicNegativeHighCutCenters G S j r).card : ℤ) := by
    exact_mod_cast hhand
  have hsubZ : ((((2 ^ j : ℕ) - r : ℕ) : ℤ)) =
      ((2 ^ j : ℕ) : ℤ) - r := by
    rw [Nat.cast_sub (by omega)]
  rw [hsubZ] at hhandZ
  nlinarith

end

end Erdos85

#print axioms Erdos85.finalDyadic_defectCutDegree_highClasses_handshake
#print axioms Erdos85.finalDyadic_defectCutDegree_highClasses_card_sub
