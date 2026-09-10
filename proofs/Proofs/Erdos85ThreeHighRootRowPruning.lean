import Proofs.Erdos85ThreeHighDegreeFirstDFS

namespace Erdos85

def threeHighRootRowGate (S : Finset (Fin 8)) : Bool :=
  decide ((S.filter fun j => j.val < 6).card ≤ 1)

theorem threeHighRootRowGate_of_c4
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross)
    (hC4 : encodedC4Free (threeHighEmptyAdj UAdj RAdj cross) = true) (i : Fin 15) :
    threeHighRootRowGate (threeHighCrossRows cross i) = true := by
  unfold encodedC4Free at hC4
  simp only [decide_eq_true_eq] at hC4
  have h := hC4
  have hi : threeHighEmptyUIndex i ≠ 23 := by
    intro he
    have hv := congrArg Fin.val he
    simp only [threeHighEmptyUIndex, Fin.val_castAdd] at hv
    have := i.isLt
    omega
  have hc := h (threeHighEmptyUIndex i) 23 hi
  apply decide_eq_true_iff.mpr
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have hmem (j : Fin 8)
      (hj : j ∈ (threeHighCrossRows cross i).filter (fun j => j.val < 6)) :
      threeHighEmptyRIndex j ∈ Finset.univ.filter (fun x =>
        threeHighEmptyAdj UAdj RAdj cross (threeHighEmptyUIndex i) x &&
        threeHighEmptyAdj UAdj RAdj cross 23 x) := by
    have hj' := Finset.mem_filter.mp hj
    have hx : cross i j = true := by simpa [threeHighCrossRows] using hj'.1
    simp [threeHighEmptyAdj, hx, hj'.2]
  have he := Finset.card_le_one.mp hc _ (hmem a ha) _ (hmem b hb)
  apply Fin.ext
  have hv := congrArg Fin.val he
  simpa [threeHighEmptyRIndex] using hv

def threeHighRootPrunedRowList (UAdj : Fin 15 → Fin 15 → Bool) (i : Fin 15) :
    List (Finset (Fin 8)) :=
  (threeHighCrossRowList UAdj i).filter threeHighRootRowGate

attribute [local irreducible] threeHighCrossDomain

theorem threeHighRootPrunedRowList_complete
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain UAdj RAdj) (i : Fin 15) :
    threeHighCrossRows cross i ∈ threeHighRootPrunedRowList UAdj i := by
  apply List.mem_filter.mpr
  refine ⟨threeHighCrossRowList_complete UAdj i _
    ((threeHighCrossDomain_rows UAdj RAdj cross hc).2 i), ?_⟩
  exact threeHighRootRowGate_of_c4 UAdj RAdj cross
    ((mem_threeHighCrossDomain_iff UAdj RAdj cross).mp hc).1 i

def threeHighRootPrunedDFS (UAdj : Fin 15 → Fin 15 → Bool)
    (RAdj : Fin 8 → Fin 8 → Bool) (accept : ThreeHighCross → Bool) : Bool :=
  finiteRowDFS (threeHighRootPrunedRowList UAdj)
    (fun k rows =>
      let cross := threeHighCrossOfRows rows
      threeHighCrossCapacity RAdj cross && threeHighCrossCanFill RAdj cross k &&
        encodedC4FreeCachedRows (threeHighEmptyAdj UAdj RAdj cross))
    (fun rows =>
      let cross := threeHighCrossOfRows rows
      encodedDegreeProfile (threeHighEmptyAdj UAdj RAdj cross)
        (fun i => if i = 23 then 6 else 4) && accept cross)
    15 0 (fun _ => ∅)



private theorem prefix_encode (cross : ThreeHighCross) (k : ℕ) :
    threeHighCrossOfRows (finiteRowPrefix (fun _ => ∅) (threeHighCrossRows cross) k) =
      threeHighCrossPrefix cross k := by
  funext i j
  by_cases hi : i.val < k <;>
    simp [threeHighCrossOfRows, finiteRowPrefix, threeHighCrossRows, threeHighCrossPrefix, hi]

attribute [local irreducible] encodedC4Free encodedDegreeProfile
  threeHighCrossCapacity threeHighCrossCanFill threeHighCrossRowDomain

theorem threeHighRootPrunedDFS_witness
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (accept : ThreeHighCross → Bool) (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain UAdj RAdj) (ha : accept cross = true) :
    threeHighRootPrunedDFS UAdj RAdj accept = true := by
  apply finiteRowDFS_witness _ _ _ (fun _ => ∅) (threeHighCrossRows cross)
  · intro i
    exact threeHighRootPrunedRowList_complete UAdj RAdj cross hc i
  · intro k hk
    rw [prefix_encode]
    simp only [Bool.and_eq_true, encodedC4FreeCachedRows_eq]
    exact ⟨⟨threeHighCrossDomain_prefix_capacity UAdj RAdj cross hc k,
      threeHighCrossDomain_prefix_canFill UAdj RAdj cross hc k⟩,
      threeHighCrossDomain_prefix_c4 UAdj RAdj cross hc k⟩
  · rw [threeHighCrossOfRows_rows]
    simp only [Bool.and_eq_true]
    exact ⟨((mem_threeHighCrossDomain_iff UAdj RAdj cross).mp hc).2, ha⟩

end Erdos85
#print axioms Erdos85.threeHighRootRowGate_of_c4
#print axioms Erdos85.threeHighRootPrunedRowList_complete

#print axioms Erdos85.threeHighRootPrunedDFS_witness
