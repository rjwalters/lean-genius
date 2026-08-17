import Proofs.Erdos85BinarySquareRegularParity

/-!
# The genuine regular partition frontier at order 64

At even square degree, normalized-size-one defect components are impossible.
For `q=8`, the normalized component sizes therefore partition eight into
parts at least two, so there are at most four components.  This file packages
that corrected regular frontier and resolves its maximal-component census.
-/

open SimpleGraph

namespace Erdos85

/-- A regular C4-free order-64 candidate has normalized defect-component
sizes at least two summing to eight, and hence at most four components. -/
theorem orderSixtyFour_regular_defectComponent_partition_package
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8) :
    ∃ m : (secondOrderDefectGraph G).ConnectedComponent → ℕ,
      (∀ c, c.supp.ncard = 8 * m c) ∧
      (∑ c, m c = 8) ∧
      (∀ c, 2 ≤ m c) ∧
      Fintype.card (secondOrderDefectGraph G).ConnectedComponent ≤ 4 := by
  have hcard : Fintype.card (Fin 64) = 8 * 8 := by norm_num
  obtain ⟨m, hmSize, hmSum⟩ :=
    binarySquare_regular_exists_defectComponent_partition
      G hfree (q := 8) (by norm_num) hreg hcard
  have hmLower : ∀ c, 2 ≤ m c := by
    intro c
    have hmPos : 0 < m c := by
      have hcPos := c.nonempty_supp.ncard_pos
      rw [hmSize c] at hcPos
      omega
    have hmNe : m c ≠ 1 := by
      intro hmOne
      have hcEight : c.supp.ncard = 8 := by simpa [hmOne] using hmSize c
      exact binarySquare_regular_no_sizeQ_defectComponent_of_even
        G hfree (q := 8) (by norm_num) (by exact ⟨4, by norm_num⟩)
          hreg hcard c hcEight
    omega
  have hcount :
      Fintype.card (secondOrderDefectGraph G).ConnectedComponent ≤ 4 := by
    have h := binarySquare_regular_two_mul_card_defectComponents_le
      G hfree (q := 8) (by norm_num) (by exact ⟨4, by norm_num⟩) hreg hcard
    omega
  exact ⟨m, hmSize, hmSum, hmLower, hcount⟩

/-- In the maximal four-component regular branch, all normalized parts are
two; equivalently, all four defect components have order sixteen. -/
theorem orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4) :
    ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16 := by
  classical
  obtain ⟨m, hmSize, hmSum, hmLower, _hcountLe⟩ :=
    orderSixtyFour_regular_defectComponent_partition_package G hfree hreg
  intro c
  have hcmem : c ∈ (Finset.univ : Finset
      (secondOrderDefectGraph G).ConnectedComponent) := Finset.mem_univ c
  have hrest : 6 ≤ ∑ d ∈ (Finset.univ.erase c), m d := by
    calc
      6 = ∑ _d ∈ (Finset.univ.erase c : Finset
          (secondOrderDefectGraph G).ConnectedComponent), 2 := by
            simp [hcount]
      _ ≤ ∑ d ∈ (Finset.univ.erase c), m d := by
        exact Finset.sum_le_sum fun d _hd => hmLower d
  have hsplit : (∑ d ∈ (Finset.univ.erase c), m d) + m c = 8 := by
    exact (Finset.sum_erase_add _ _ hcmem).trans hmSum
  have hcLower := hmLower c
  have hmc : m c = 2 := by omega
  rw [hmSize c, hmc]

end Erdos85
