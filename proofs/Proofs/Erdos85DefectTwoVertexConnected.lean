import Proofs.Erdos85DefectMaxEdgeConnectivity
import Proofs.Erdos85DeletedOwnerShoreClassification

/-!
# No articulation vertex in the connected defect graph

Maximal defect edge connectivity closes the previously exposed deleted-owner
cut budget: two positive complementary shores cannot have boundaries summing
to only `q - 1` when each boundary is already at least `q - 1`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In the binary-square connected branch, deleting any vertex leaves the
induced second-order defect graph connected. -/
theorem binarySquare_connected_secondOrderDefect_erase_connected
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Connected) (owner : V) :
    ((secondOrderDefectGraph G).induce
      (↑((Finset.univ : Finset V).erase owner) : Set V)).Connected := by
  let D := secondOrderDefectGraph G
  have hpunctured : ((Finset.univ : Finset V).erase owner).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hcardErase := congrArg Finset.card hempty
    simp only [Finset.card_erase_of_mem (Finset.mem_univ owner),
      Finset.card_univ, Finset.card_empty] at hcardErase
    rw [hcard] at hcardErase
    have hqq : 1 < q * q := by nlinarith
    omega
  by_contra hnot
  obtain ⟨S, T, _hS, _hT, _hunion, _hdisj, _hSclosed, _hTclosed,
      hSpos, hTpos, hsum⟩ :=
    binarySquare_regular_exists_punctured_shores_boundary_sum_eq_q_sub_one
      G hfree hq hreg hcard owner hconn hpunctured hnot
  have hcutEq (R : Finset V) :
      (∑ x ∈ R, (D.neighborFinset x ∩ (Finset.univ \ R)).card) =
        finsetGraphCutSize D R := by
    unfold finsetGraphCutSize
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    ext z
    simp
  have hSpos' : 0 < finsetGraphCutSize D S := by
    rw [← hcutEq]
    simpa [D] using hSpos
  have hTpos' : 0 < finsetGraphCutSize D T := by
    rw [← hcutEq]
    simpa [D] using hTpos
  have hSlower : q - 1 ≤ finsetGraphCutSize D S := by
    simpa [D] using binarySquare_regular_pred_le_defectCut_of_pos
      G hfree hq hreg hcard S (by simpa [D] using hSpos')
  have hTlower : q - 1 ≤ finsetGraphCutSize D T := by
    simpa [D] using binarySquare_regular_pred_le_defectCut_of_pos
      G hfree hq hreg hcard T (by simpa [D] using hTpos')
  have hsum' : finsetGraphCutSize D S + finsetGraphCutSize D T = q - 1 := by
    rw [← hcutEq, ← hcutEq]
    simpa [D] using hsum
  omega

#print axioms binarySquare_connected_secondOrderDefect_erase_connected

end

end Erdos85
