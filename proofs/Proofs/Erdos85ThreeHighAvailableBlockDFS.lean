import Proofs.Erdos85AvailableBlockDeficit
import Proofs.Erdos85ThreeHighBlockDeficit

namespace Erdos85

attribute [local irreducible] threeHighCrossDomain

theorem threeHighExternalCap_prefix_availableCanFill
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain UAdj RAdj)
    (hExt : encodedExternalBlockCap (threeHighEmptyAdj UAdj RAdj cross) threeHighCanonicalRow = true)
    (k : Nat) :
    threeHighCrossAvailableCanFill RAdj (threeHighCrossPrefix cross k) k threeHighUBlock = true := by
  rw [threeHighExternalBlockCap_factor, Bool.and_eq_true] at hExt
  exact threeHighCrossDomain_prefix_availableCanFill UAdj RAdj cross hc threeHighUBlock
    (threeHighCrossBlockCap_fibers cross hExt.2) k

/-- Exclude blocks already used by an assigned neighbor when testing column deficits. -/
def threeHighAvailableBlockDFS (UAdj : Fin 15 → Fin 15 → Bool)
    (RAdj : Fin 8 → Fin 8 → Bool) (accept : ThreeHighCross → Bool) : Bool :=
  let fixedCap := threeHighUnionBlockCap UAdj
  finiteRowDFS (threeHighRootPrunedRowList UAdj)
    (fun k rows =>
      let cross := threeHighCrossOfRows rows
      threeHighCrossCapacity RAdj cross &&
        threeHighCrossAvailableCanFill RAdj cross k threeHighUBlock &&
        (fixedCap && threeHighCrossBlockCap cross) &&
        encodedC4FreeCachedRows (threeHighEmptyAdj UAdj RAdj cross))
    (fun rows =>
      let cross := threeHighCrossOfRows rows
      encodedDegreeProfile (threeHighEmptyAdj UAdj RAdj cross)
        (fun i => if i = 23 then 6 else 4) && accept cross)
    15 0 (fun _ => ∅)

private theorem prefix_encode (cross : ThreeHighCross) (k : Nat) :
    threeHighCrossOfRows (finiteRowPrefix (fun _ => ∅) (threeHighCrossRows cross) k) =
      threeHighCrossPrefix cross k := by
  funext i j
  by_cases hi : i.val < k <;>
    simp [threeHighCrossOfRows,finiteRowPrefix,threeHighCrossRows,threeHighCrossPrefix,hi]

theorem threeHighAvailableBlockDFS_witness
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (accept : ThreeHighCross → Bool) (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain UAdj RAdj)
    (hExt : encodedExternalBlockCap (threeHighEmptyAdj UAdj RAdj cross) threeHighCanonicalRow = true)
    (ha : accept cross = true) : threeHighAvailableBlockDFS UAdj RAdj accept = true := by
  unfold threeHighAvailableBlockDFS
  dsimp only
  apply finiteRowDFS_witness _ _ _ (fun _ => ∅) (threeHighCrossRows cross)
  · intro i
    exact threeHighRootPrunedRowList_complete UAdj RAdj cross hc i
  · intro k hk
    rw [prefix_encode]
    have he := threeHighExternalBlockCap_prefix UAdj RAdj cross threeHighCanonicalRow hExt k
    rw [threeHighExternalBlockCap_factor] at he
    simp only [Bool.and_eq_true,encodedC4FreeCachedRows_eq]
    exact ⟨⟨⟨threeHighCrossDomain_prefix_capacity UAdj RAdj cross hc k,
      threeHighExternalCap_prefix_availableCanFill UAdj RAdj cross hc hExt k⟩,
      (by simpa only [Bool.and_eq_true] using he)⟩,threeHighCrossDomain_prefix_c4 UAdj RAdj cross hc k⟩
  · rw [threeHighCrossOfRows_rows]
    simp only [Bool.and_eq_true]
    exact ⟨((mem_threeHighCrossDomain_iff UAdj RAdj cross).mp hc).2,ha⟩

end Erdos85
#print axioms Erdos85.threeHighExternalCap_prefix_availableCanFill
#print axioms Erdos85.threeHighAvailableBlockDFS_witness
