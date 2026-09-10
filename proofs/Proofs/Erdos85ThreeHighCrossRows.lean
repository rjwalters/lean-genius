import Proofs.Erdos85ThreeHighCrossMargins

namespace Erdos85

def threeHighCrossRowDomain (UAdj : Fin 15 → Fin 15 → Bool) (i : Fin 15) :
    Finset (Finset (Fin 8)) :=
  Finset.univ.powersetCard (4 - encodedRowDegree (UAdj i))

def threeHighCrossRows (cross : ThreeHighCross) : Fin 15 → Finset (Fin 8) :=
  fun i => Finset.univ.filter fun j => cross i j

def threeHighCrossOfRows (rows : Fin 15 → Finset (Fin 8)) : ThreeHighCross :=
  fun i j => decide (j ∈ rows i)

theorem threeHighCrossOfRows_rows (cross : ThreeHighCross) :
    threeHighCrossOfRows (threeHighCrossRows cross) = cross := by
  funext i j
  simp [threeHighCrossOfRows, threeHighCrossRows]

attribute [local irreducible] threeHighCrossDomain encodedC4Free encodedDegreeProfile

theorem threeHighCrossDomain_rows
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain UAdj RAdj) :
    (∀ i, encodedRowDegree (UAdj i) ≤ 4) ∧
    (∀ i, threeHighCrossRows cross i ∈ threeHighCrossRowDomain UAdj i) := by
  have hm := (threeHighCrossDomain_margins UAdj RAdj cross hc).1
  constructor
  · intro i
    have h := hm i
    omega
  · intro i
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    have h := hm i
    change encodedRowDegree (cross i) = 4 - encodedRowDegree (UAdj i)
    omega

/-- Every valid incidence matrix is reconstructed from prescribed-size row choices. -/
theorem threeHighCrossDomain_row_cover
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain UAdj RAdj) :
    ∃ rows : Fin 15 → Finset (Fin 8),
      (∀ i, rows i ∈ threeHighCrossRowDomain UAdj i) ∧ threeHighCrossOfRows rows = cross := by
  exact ⟨threeHighCrossRows cross, (threeHighCrossDomain_rows UAdj RAdj cross hc).2,
    threeHighCrossOfRows_rows cross⟩

end Erdos85
#print axioms Erdos85.threeHighCrossOfRows_rows
#print axioms Erdos85.threeHighCrossDomain_rows
#print axioms Erdos85.threeHighCrossDomain_row_cover
