import Proofs.Erdos85TwoSeparatorCutBudget
import Proofs.Erdos85ConnectedClosedNeighborhoodEscape

/-!
# Rigidity of a two-separator shore partition

For a connected second-order defect graph, an explicit partition into two
nonempty shores and a two-vertex separator forces both shore cuts to attain
the minimum `q-1`. Their square-order residues are then both `q-1`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Every nonempty proper shore of a connected finite graph has positive
finite-set cut size. -/
theorem finsetGraphCutSize_pos_of_connected_nonempty_proper
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (hconn : D.Connected)
    (S : Finset V) (hSne : S.Nonempty)
    (hSproper : (↑S : Set V) ≠ Set.univ) :
    0 < finsetGraphCutSize D S := by
  obtain ⟨x, hxS, y, hyS, hxy⟩ :=
    connected_exists_adj_outside_of_nonempty_proper
      D hconn (↑S : Set V) (by simpa using hSne) hSproper
  unfold finsetGraphCutSize
  apply Finset.sum_pos' (fun _ _ => Nat.zero_le _)
  refine ⟨x, by simpa using hxS, Finset.card_pos.mpr ⟨y, ?_⟩⟩
  exact Finset.mem_sdiff.mpr ⟨
    (SimpleGraph.mem_neighborFinset D x y).mpr hxy, by simpa using hyS⟩

/-- A two-shore partition behind a two-vertex separator consists of two
minimum cuts, and both shores have residue `-1` modulo `q`. -/
theorem binarySquare_twoSeparator_partition_cut_and_residue_rigidity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 8 ≤ q)
    (hqEven : Even q) (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Connected)
    (S T W : Finset V)
    (hcover : S ∪ T ∪ W = Finset.univ)
    (hST : Disjoint S T) (hno : ∀ s ∈ S, ∀ t ∈ T,
      ¬ (secondOrderDefectGraph G).Adj s t)
    (hSne : S.Nonempty) (hTne : T.Nonempty)
    (hWcard : W.card = 2)
    (hcards : S.card + T.card = q * q - 2) :
    finsetGraphCutSize (secondOrderDefectGraph G) S = q - 1 ∧
      finsetGraphCutSize (secondOrderDefectGraph G) T = q - 1 ∧
      S.card % q = q - 1 ∧ T.card % q = q - 1 := by
  let D := secondOrderDefectGraph G
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDreg : ∀ x, D.degree x = q - 1 := by
    intro x
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus x
    change D.degree x = (q - 3) + 2 at h
    omega
  have hSproper : (↑S : Set V) ≠ Set.univ := by
    intro hSu
    obtain ⟨t, htT⟩ := hTne
    have htS : t ∈ S := by
      have : t ∈ (↑S : Set V) := by rw [hSu]; trivial
      simpa using this
    exact Finset.disjoint_left.mp hST htS htT
  have hTproper : (↑T : Set V) ≠ Set.univ := by
    intro hTu
    obtain ⟨s, hsS⟩ := hSne
    have hsT : s ∈ T := by
      have : s ∈ (↑T : Set V) := by rw [hTu]; trivial
      simpa using this
    exact Finset.disjoint_left.mp hST hsS hsT
  have hSpos : 0 < finsetGraphCutSize D S :=
    finsetGraphCutSize_pos_of_connected_nonempty_proper D hconn S hSne hSproper
  have hTpos : 0 < finsetGraphCutSize D T :=
    finsetGraphCutSize_pos_of_connected_nonempty_proper D hconn T hTne hTproper
  have hSlower : q - 1 ≤ finsetGraphCutSize D S := by
    simpa [D] using binarySquare_regular_pred_le_defectCut_of_pos
      G hfree (by omega : 3 ≤ q) hreg hcard S (by simpa [D] using hSpos)
  have hTlower : q - 1 ≤ finsetGraphCutSize D T := by
    simpa [D] using binarySquare_regular_pred_le_defectCut_of_pos
      G hfree (by omega : 3 ≤ q) hreg hcard T (by simpa [D] using hTpos)
  have hbudget : finsetGraphCutSize D S + finsetGraphCutSize D T ≤
      2 * (q - 1) := by
    exact add_finsetGraphCutSize_le_two_mul_degree_of_twoSeparator
      D S T W hcover hST (by simpa [D] using hno) hWcard hDreg
  have hcutS : finsetGraphCutSize D S = q - 1 := by omega
  have hcutT : finsetGraphCutSize D T = q - 1 := by omega
  have hres := binarySquare_two_predCuts_both_card_mod_eq_pred
    G hfree hq hqEven hreg hcard S T hcards
    (by simpa [D] using hcutS) (by simpa [D] using hcutT)
  exact ⟨by simpa [D] using hcutS, by simpa [D] using hcutT, hres⟩

#print axioms finsetGraphCutSize_pos_of_connected_nonempty_proper
#print axioms binarySquare_twoSeparator_partition_cut_and_residue_rigidity

end

end Erdos85
