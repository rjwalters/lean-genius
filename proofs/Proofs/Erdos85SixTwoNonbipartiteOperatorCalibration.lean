import Proofs.Erdos85BinarySquareRegularParity

/-! # A non-bipartite calibration for the `[6,2]` operator data

The elementary operator package in a normalized size-two component does not
by itself force the defect block to be bipartite.  The explicit circulants
below give a connected non-bipartite 7-regular graph `D` on sixteen vertices
whose off-diagonal complement splits into commuting 6- and 2-regular graphs.
The 2-regular graph is a sixteen-cycle, so it is itself C4-free.
Consequently, a proof of bipartiteness in the order-64 `[6,2]` stratum must use
the selector/line-graph or ambient common-neighbor geometry, not only degrees,
edge partition, and matrix commutation.
-/

open SimpleGraph Matrix

namespace Erdos85

set_option maxHeartbeats 0

/-- Directed cyclic difference on `Fin 16`, represented in `0, ..., 15`. -/
def fin16CyclicDiff (x y : Fin 16) : ℕ := (y.val + 16 - x.val) % 16

/-- Seven-regular defect calibration: connection steps
`±2, ±3, ±4, 8`. -/
def sixTwoCalibrationDefect : SimpleGraph (Fin 16) where
  Adj x y :=
    fin16CyclicDiff x y = 2 ∨ fin16CyclicDiff x y = 3 ∨
    fin16CyclicDiff x y = 4 ∨ fin16CyclicDiff x y = 8 ∨
    fin16CyclicDiff x y = 12 ∨ fin16CyclicDiff x y = 13 ∨
    fin16CyclicDiff x y = 14
  symm := by
    constructor
    intro x y
    fin_cases x <;> fin_cases y <;> simp_all [fin16CyclicDiff]
  loopless := by
    constructor
    intro x
    fin_cases x <;> simp_all [fin16CyclicDiff]

/-- Two-factor calibration: connection steps `±1`, hence a sixteen-cycle. -/
def sixTwoCalibrationSmallOwner : SimpleGraph (Fin 16) where
  Adj x y := fin16CyclicDiff x y = 1 ∨ fin16CyclicDiff x y = 15
  symm := by
    constructor
    intro x y
    fin_cases x <;> fin_cases y <;> simp_all [fin16CyclicDiff]
  loopless := by
    constructor
    intro x
    fin_cases x <;> simp_all [fin16CyclicDiff]

/-- Six-factor calibration: the remaining connection steps
`±5, ±6, ±7`. -/
def sixTwoCalibrationLargeOwner : SimpleGraph (Fin 16) where
  Adj x y :=
    fin16CyclicDiff x y = 5 ∨ fin16CyclicDiff x y = 6 ∨
    fin16CyclicDiff x y = 7 ∨ fin16CyclicDiff x y = 9 ∨
    fin16CyclicDiff x y = 10 ∨ fin16CyclicDiff x y = 11
  symm := by
    constructor
    intro x y
    fin_cases x <;> fin_cases y <;> simp_all [fin16CyclicDiff]
  loopless := by
    constructor
    intro x
    fin_cases x <;> simp_all [fin16CyclicDiff]

instance : DecidableRel sixTwoCalibrationDefect.Adj := by
  intro x y
  change Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _)
  infer_instance
instance : DecidableRel sixTwoCalibrationSmallOwner.Adj := by
  intro x y
  change Decidable (_ ∨ _)
  infer_instance
instance : DecidableRel sixTwoCalibrationLargeOwner.Adj := by
  intro x y
  change Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _)
  infer_instance

theorem sixTwoCalibrationDefect_degree : ∀ x : Fin 16,
    sixTwoCalibrationDefect.degree x = 7 := by decide

theorem sixTwoCalibrationSmallOwner_degree : ∀ x : Fin 16,
    sixTwoCalibrationSmallOwner.degree x = 2 := by decide

/-- The small-owner two-factor calibration is C4-free.  This is not the
internal ambient graph; `4da8c82eed` supplies the stronger self-source
calibration with an explicit C4-free internal factor. -/
theorem sixTwoCalibrationSmallOwner_c4Free :
    ¬ containsC4 (Fin 16) sixTwoCalibrationSmallOwner := by
  have heq : sixTwoCalibrationSmallOwner = cycleGraph 16 := by
    ext x y
    fin_cases x <;> fin_cases y <;> decide
  rw [heq]
  exact cycleGraph_not_containsC4 (by omega)

theorem sixTwoCalibrationLargeOwner_degree : ∀ x : Fin 16,
    sixTwoCalibrationLargeOwner.degree x = 6 := by decide

/-- The three graphs partition every unordered pair. -/
theorem sixTwoCalibration_exact_edge_partition (x y : Fin 16) (hxy : x ≠ y) :
    (sixTwoCalibrationDefect.Adj x y ∧
        ¬ sixTwoCalibrationSmallOwner.Adj x y ∧
        ¬ sixTwoCalibrationLargeOwner.Adj x y) ∨
    (¬ sixTwoCalibrationDefect.Adj x y ∧
        sixTwoCalibrationSmallOwner.Adj x y ∧
        ¬ sixTwoCalibrationLargeOwner.Adj x y) ∨
    (¬ sixTwoCalibrationDefect.Adj x y ∧
        ¬ sixTwoCalibrationSmallOwner.Adj x y ∧
        sixTwoCalibrationLargeOwner.Adj x y) := by
  fin_cases x <;> fin_cases y <;> simp_all [sixTwoCalibrationDefect,
    sixTwoCalibrationSmallOwner, sixTwoCalibrationLargeOwner, fin16CyclicDiff]

/-- The defect calibration is connected. -/
theorem sixTwoCalibrationDefect_connected : sixTwoCalibrationDefect.Connected := by
  decide

/-- The vertices `0,2,4` form a triangle, so the defect calibration is not
bipartite. -/
theorem sixTwoCalibrationDefect_not_bipartite :
    ¬ sixTwoCalibrationDefect.IsBipartite := by
  intro h
  obtain ⟨col, hcol⟩ := h
  have h02 : col (0 : Fin 16) ≠ col (2 : Fin 16) := hcol (by decide)
  have h24 : col (2 : Fin 16) ≠ col (4 : Fin 16) := hcol (by decide)
  have h04 : col (0 : Fin 16) ≠ col (4 : Fin 16) := hcol (by decide)
  have h02v : (col (0 : Fin 16)).val ≠ (col (2 : Fin 16)).val :=
    fun h => h02 (Fin.ext h)
  have h24v : (col (2 : Fin 16)).val ≠ (col (4 : Fin 16)).val :=
    fun h => h24 (Fin.ext h)
  have h04v : (col (0 : Fin 16)).val ≠ (col (4 : Fin 16)).val :=
    fun h => h04 (Fin.ext h)
  omega

/-- All three adjacency matrices commute pairwise over the integers. -/
theorem sixTwoCalibration_adjMatrices_commute :
    Commute (sixTwoCalibrationDefect.adjMatrix ℤ)
        (sixTwoCalibrationSmallOwner.adjMatrix ℤ) ∧
      Commute (sixTwoCalibrationDefect.adjMatrix ℤ)
        (sixTwoCalibrationLargeOwner.adjMatrix ℤ) ∧
      Commute (sixTwoCalibrationSmallOwner.adjMatrix ℤ)
        (sixTwoCalibrationLargeOwner.adjMatrix ℤ) := by
  have hDF : ∀ i j : Fin 16,
      (sixTwoCalibrationDefect.adjMatrix ℤ *
          sixTwoCalibrationSmallOwner.adjMatrix ℤ) i j =
        (sixTwoCalibrationSmallOwner.adjMatrix ℤ *
          sixTwoCalibrationDefect.adjMatrix ℤ) i j := by decide
  have hDB : ∀ i j : Fin 16,
      (sixTwoCalibrationDefect.adjMatrix ℤ *
          sixTwoCalibrationLargeOwner.adjMatrix ℤ) i j =
        (sixTwoCalibrationLargeOwner.adjMatrix ℤ *
          sixTwoCalibrationDefect.adjMatrix ℤ) i j := by decide
  have hFB : ∀ i j : Fin 16,
      (sixTwoCalibrationSmallOwner.adjMatrix ℤ *
          sixTwoCalibrationLargeOwner.adjMatrix ℤ) i j =
        (sixTwoCalibrationLargeOwner.adjMatrix ℤ *
          sixTwoCalibrationSmallOwner.adjMatrix ℤ) i j := by decide
  refine ⟨?_, ?_, ?_⟩ <;> rw [commute_iff_eq] <;> ext i j
  · exact hDF i j
  · exact hDB i j
  · exact hFB i j

#print axioms Erdos85.sixTwoCalibrationDefect_degree
#print axioms Erdos85.sixTwoCalibrationSmallOwner_degree
#print axioms Erdos85.sixTwoCalibrationSmallOwner_c4Free
#print axioms Erdos85.sixTwoCalibrationLargeOwner_degree
#print axioms Erdos85.sixTwoCalibration_exact_edge_partition
#print axioms Erdos85.sixTwoCalibrationDefect_connected
#print axioms Erdos85.sixTwoCalibrationDefect_not_bipartite
#print axioms Erdos85.sixTwoCalibration_adjMatrices_commute

end Erdos85
