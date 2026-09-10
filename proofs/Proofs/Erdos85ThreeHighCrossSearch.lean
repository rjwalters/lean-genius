import Proofs.Erdos85ThreeHighCrossRows
import Proofs.Erdos85ThreeHighCrossPruning

namespace Erdos85

abbrev ThreeHighRows := Fin 15 → Finset (Fin 8)

def threeHighRowsPrefix (rows : ThreeHighRows) (k : ℕ) : ThreeHighRows :=
  fun i => if i.val < k then rows i else ∅

/-- Breadth-first row extension with exact row sizes and partial C4 rejection.
This is an executable specification, not a claim that its full evaluation is cheap. -/
def threeHighCrossSearch (UAdj : Fin 15 → Fin 15 → Bool)
    (RAdj : Fin 8 → Fin 8 → Bool) : ℕ → Finset ThreeHighRows
  | 0 => {fun _ => ∅}
  | k + 1 => if h : k < 15 then
      ((threeHighCrossSearch UAdj RAdj k).biUnion fun rows =>
        (threeHighCrossRowDomain UAdj ⟨k, h⟩).image fun row =>
          Function.update rows ⟨k, h⟩ row).filter fun rows =>
            encodedC4Free (threeHighEmptyAdj UAdj RAdj (threeHighCrossOfRows rows)) = true
    else ∅

private theorem rowsPrefix_succ (rows : ThreeHighRows) (k : ℕ) (hk : k < 15) :
    threeHighRowsPrefix rows (k + 1) =
      Function.update (threeHighRowsPrefix rows k) ⟨k, hk⟩ (rows ⟨k, hk⟩) := by
  funext i
  by_cases hi : i = ⟨k, hk⟩
  · subst i
    simp [threeHighRowsPrefix]
  · have hne : i.val ≠ k := fun h => hi (Fin.ext h)
    have he : (i.val < k + 1) ↔ i.val < k := by omega
    simp [Function.update_of_ne hi, threeHighRowsPrefix, he]

private theorem rowsPrefix_encode (cross : ThreeHighCross) (k : ℕ) :
    threeHighCrossOfRows (threeHighRowsPrefix (threeHighCrossRows cross) k) =
      threeHighCrossPrefix cross k := by
  funext i j
  by_cases hi : i.val < k <;>
    simp [threeHighCrossOfRows, threeHighRowsPrefix, threeHighCrossRows,
      threeHighCrossPrefix, hi]

attribute [local irreducible] threeHighCrossDomain encodedC4Free encodedDegreeProfile
  threeHighCrossRowDomain

theorem threeHighCrossSearch_prefix_cover
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain UAdj RAdj)
    (k : ℕ) (hk : k ≤ 15) :
    threeHighRowsPrefix (threeHighCrossRows cross) k ∈ threeHighCrossSearch UAdj RAdj k := by
  induction k with
  | zero =>
    simp only [threeHighCrossSearch, Finset.mem_singleton]
    funext i
    simp only [threeHighRowsPrefix, Nat.not_lt_zero, if_false]
  | succ k ih =>
    have hk' : k < 15 := by omega
    rw [threeHighCrossSearch, dif_pos hk']
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_biUnion.mpr
      refine ⟨threeHighRowsPrefix (threeHighCrossRows cross) k, ih (by omega), ?_⟩
      apply Finset.mem_image.mpr
      exact ⟨threeHighCrossRows cross ⟨k, hk'⟩,
        (threeHighCrossDomain_rows UAdj RAdj cross hc).2 _,
        (rowsPrefix_succ _ k hk').symm⟩
    · rw [rowsPrefix_encode]
      exact threeHighCrossDomain_prefix_c4 UAdj RAdj cross hc (k + 1)

theorem threeHighCrossSearch_cover
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain UAdj RAdj) :
    ∃ rows ∈ threeHighCrossSearch UAdj RAdj 15, threeHighCrossOfRows rows = cross := by
  refine ⟨threeHighCrossRows cross, ?_, threeHighCrossOfRows_rows cross⟩
  have h := threeHighCrossSearch_prefix_cover UAdj RAdj cross hc 15 (by omega)
  have he : threeHighRowsPrefix (threeHighCrossRows cross) 15 = threeHighCrossRows cross := by
    funext i
    simp only [threeHighRowsPrefix, if_pos i.isLt]
  rwa [he] at h

end Erdos85
#print axioms Erdos85.threeHighCrossSearch_prefix_cover
#print axioms Erdos85.threeHighCrossSearch_cover
