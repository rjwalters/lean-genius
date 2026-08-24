import Proofs.Erdos85MinimumDefectCutLowSetCutIdentity
import Proofs.Erdos85MinimumDefectCutNearMantelArithmetic
import Proofs.Erdos85ClosedNeighborhoodCutTriangleIdentity
import Proofs.Erdos85ThreeLevelEigenSupportEdgeCensus
import Proofs.Erdos85MinimumCutEraseVertexCap
import Proofs.Erdos85TwoSeparatorCutRigidity

/-! # Graph-facing near-Mantel lower for a minimum-cut low set -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Equation (7), the minimum-cut boundary cap, and the regular handshake
give the near-Mantel lower bound for the associated q-set. -/
theorem binarySquare_minimumCut_lowSet_nearMantel_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q r a : ℕ}
    (hr : 2 ≤ r) (hq : q = 2 * (r + 1))
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDreg : ∀ x, (secondOrderDefectGraph G).degree x = q - 1)
    (S Z : Finset V) (hScard : S.card = q * a + 1)
    (hcutS : finsetGraphCutSize (secondOrderDefectGraph G) S = q - 1)
    (hcap : ∀ x ∈ S,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ S)).card ≤ r)
    (hocc : ∀ x, (G.neighborFinset x ∩ S).card =
      a + if x ∈ Z then 1 else 0) :
    q ^ 2 - 4 ≤
      4 * ((secondOrderDefectGraph G).induce (↑Z : Set V)).edgeFinset.card := by
  let D := secondOrderDefectGraph G
  let d : V → ℕ := fun x => if x ∈ S then
    (D.neighborFinset x ∩ (Finset.univ \ S)).card else 0
  have hZcard : Z.card = q := by
    have hsum : (∑ x : V, (G.neighborFinset x ∩ S).card) = q * S.card := by
      rw [sum_card_neighbor_inter_eq_sum_degree]
      calc
        (∑ x ∈ S, G.degree x) = ∑ _x ∈ S, q := by
          apply Finset.sum_congr rfl
          intro x _
          exact hreg x
        _ = q * S.card := by simp [mul_comm]
    simp_rw [hocc] at hsum
    rw [Finset.sum_add_distrib] at hsum
    simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul] at hsum
    have hind : (∑ x : V, if x ∈ Z then 1 else 0) = Z.card := by simp
    rw [hind, hScard] at hsum
    nlinarith
  have hbound : ∀ x, d x ≤ r := by
    intro x
    by_cases hx : x ∈ S
    · simpa [d, hx] using hcap x hx
    · simp [d, hx]
  have hsumd : ∑ x, d x = q - 1 := by
    rw [← hcutS]
    unfold finsetGraphCutSize
    rw [← Finset.sum_subset (Finset.subset_univ S)]
    · apply Finset.sum_congr rfl
      intro x hx
      simp only [d, hx, if_true, D]
      congr 1
      ext y
      simp
    · intro x _ hx
      simp [d, hx]
  have hcutIdentity : finsetGraphCutSize D Z =
      q - 1 + ∑ x, (d x) ^ 2 := by
    have hid := binarySquare_lowSet_defectCut_eq_shoreCut_add_sum_sq
      G hfree hreg hcard hDreg S Z hScard hocc
    rw [hcutS] at hid
    calc
      finsetGraphCutSize D Z = q - 1 +
          ∑ x ∈ S, (D.neighborFinset x ∩ (Finset.univ \ S)).card ^ 2 := by
        simpa [D] using hid
      _ = q - 1 + ∑ x, (d x) ^ 2 := by
        congr 1
        change (∑ x ∈ S,
          (D.neighborFinset x ∩ (Finset.univ \ S)).card ^ 2) =
            ∑ x ∈ Finset.univ, (d x) ^ 2
        rw [← Finset.sum_subset (Finset.subset_univ S)]
        · apply Finset.sum_congr rfl
          intro x hx
          simp [d, hx]
        · intro x _ hx
          simp [d, hx]
  have hinternal :
      (∑ x ∈ Z, (D.neighborFinset x ∩ Z).card) =
        2 * (D.induce (↑Z : Set V)).edgeFinset.card := by
    rw [← sum_internalNeighbor_card_eq_twice_induced_edges D Z]
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
  have hhandshake : finsetGraphCutSize D Z +
      2 * (D.induce (↑Z : Set V)).edgeFinset.card = q * (q - 1) := by
    have h := finsetGraphCutSize_add_sum_internal_eq_card_mul_of_regular
      D hDreg Z
    rw [hinternal, hZcard] at h
    exact h
  exact nearMantel_lower_of_cutIdentity_of_capped_boundary
    d hr hq hbound hsumd hcutIdentity hhandshake

/-- Connected-defect specialization: maximal edge-connectivity supplies the
pointwise boundary cap automatically for every nontrivial proper shore. -/
theorem binarySquare_connected_minimumCut_lowSet_nearMantel_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q r a : ℕ}
    (hr : 2 ≤ r) (hq : q = 2 * (r + 1))
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDreg : ∀ x, (secondOrderDefectGraph G).degree x = q - 1)
    (hconn : (secondOrderDefectGraph G).Connected)
    (S Z : Finset V) (hScard : S.card = q * a + 1)
    (hSnontrivial : 2 ≤ S.card)
    (hSproper : (↑S : Set V) ≠ Set.univ)
    (hcutS : finsetGraphCutSize (secondOrderDefectGraph G) S = q - 1)
    (hocc : ∀ x, (G.neighborFinset x ∩ S).card =
      a + if x ∈ Z then 1 else 0) :
    q ^ 2 - 4 ≤
      4 * ((secondOrderDefectGraph G).induce (↑Z : Set V)).edgeFinset.card := by
  let D := secondOrderDefectGraph G
  have hq8 : 3 ≤ q := by omega
  have hq2 : 2 ≤ q := by omega
  have hqEven : Even q := by
    refine ⟨r + 1, ?_⟩
    omega
  have hcap : ∀ x ∈ S,
      (D.neighborFinset x ∩ (Finset.univ \ S)).card ≤ r := by
    intro x hxS
    have hEraseNe : (S.erase x).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem hxS]
      omega
    have hEraseProper : (↑(S.erase x) : Set V) ≠ Set.univ := by
      intro hErase
      apply hSproper
      apply Set.eq_univ_of_univ_subset
      intro v _
      have hvErase : v ∈ S.erase x := by
        have : v ∈ (↑(S.erase x) : Set V) := by rw [hErase]; trivial
        exact this
      exact Finset.mem_of_mem_erase hvErase
    have hpos : 0 < finsetGraphCutSize D (S.erase x) :=
      finsetGraphCutSize_pos_of_connected_nonempty_proper
        D hconn (S.erase x) hEraseNe hEraseProper
    have hlower : q - 1 ≤ finsetGraphCutSize D (S.erase x) := by
      simpa [D] using binarySquare_regular_pred_le_defectCut_of_pos
        G hfree hq8 hreg hcard (S.erase x) (by simpa [D] using hpos)
    have hout := outDegree_le_even_sub_two_half_of_minCut_erase
      D hq2 hqEven hDreg S hxS (by simpa [D] using hcutS) hlower
    have hrEq : (q - 2) / 2 = r := by omega
    rw [← hrEq]
    have heq : D.neighborFinset x ∩ (Finset.univ \ S) =
        D.neighborFinset x \ S := by
      ext y
      simp
    rw [heq]
    exact hout
  exact binarySquare_minimumCut_lowSet_nearMantel_lower
    G hfree hr hq hreg hcard hDreg S Z hScard hcutS
      (by simpa [D] using hcap) hocc

#print axioms binarySquare_minimumCut_lowSet_nearMantel_lower
#print axioms binarySquare_connected_minimumCut_lowSet_nearMantel_lower

end

end Erdos85
