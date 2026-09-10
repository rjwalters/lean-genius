import Proofs.Erdos85EncodedExternalBlockCap
import Proofs.Erdos85ThreeHighRootRowPruning

namespace Erdos85

theorem encodedExternalBlockCap_mono
    {W K : Type*} [Fintype W] [DecidableEq W] [Fintype K]
    (A B : W → W → Bool) (blocks : K → Finset W)
    (hsub : EncodedSubgraph A B) (hB : encodedExternalBlockCap B blocks = true) :
    encodedExternalBlockCap A blocks = true := by
  unfold encodedExternalBlockCap at hB ⊢
  simp only [decide_eq_true_eq] at hB ⊢
  intro x k
  apply le_trans (Finset.card_le_card ?_) (hB x k)
  intro i hi
  obtain ⟨hi,hAi⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hi,hsub x i hAi⟩

theorem threeHighExternalBlockCap_prefix
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (blocks : Fin 3 → Finset (Fin 24))
    (hcap : encodedExternalBlockCap (threeHighEmptyAdj UAdj RAdj cross) blocks = true)
    (k : Nat) :
    encodedExternalBlockCap
      (threeHighEmptyAdj UAdj RAdj (threeHighCrossPrefix cross k)) blocks = true := by
  apply encodedExternalBlockCap_mono _ _ blocks _ hcap
  apply threeHighEmptyAdj_subgraph
  intro i j h
  by_cases hi : i.val < k
  · simpa only [threeHighCrossPrefix,if_pos hi] using h
  · simp only [threeHighCrossPrefix,if_neg hi,Bool.false_eq_true] at h

def threeHighExternalPrunedDFS (UAdj : Fin 15 → Fin 15 → Bool)
    (RAdj : Fin 8 → Fin 8 → Bool) (blocks : Fin 3 → Finset (Fin 24)) (accept : ThreeHighCross → Bool) : Bool :=
  finiteRowDFS (threeHighRootPrunedRowList UAdj)
    (fun k rows =>
      let cross := threeHighCrossOfRows rows
      threeHighCrossCapacity RAdj cross && threeHighCrossCanFill RAdj cross k &&
        encodedExternalBlockCap (threeHighEmptyAdj UAdj RAdj cross) blocks &&
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

attribute [local irreducible] threeHighCrossDomain encodedC4Free encodedDegreeProfile
  threeHighCrossCapacity threeHighCrossCanFill threeHighCrossRowDomain

theorem threeHighExternalPrunedDFS_witness
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (blocks : Fin 3 → Finset (Fin 24)) (accept : ThreeHighCross → Bool) (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain UAdj RAdj)
    (hcap : encodedExternalBlockCap (threeHighEmptyAdj UAdj RAdj cross) blocks = true) (ha : accept cross = true) :
    threeHighExternalPrunedDFS UAdj RAdj blocks accept = true := by
  apply finiteRowDFS_witness _ _ _ (fun _ => ∅) (threeHighCrossRows cross)
  · intro i
    exact threeHighRootPrunedRowList_complete UAdj RAdj cross hc i
  · intro k hk
    rw [prefix_encode]
    simp only [Bool.and_eq_true, encodedC4FreeCachedRows_eq]
    exact ⟨⟨⟨threeHighCrossDomain_prefix_capacity UAdj RAdj cross hc k,
      threeHighCrossDomain_prefix_canFill UAdj RAdj cross hc k⟩,
      threeHighExternalBlockCap_prefix UAdj RAdj cross blocks hcap k⟩,
      threeHighCrossDomain_prefix_c4 UAdj RAdj cross hc k⟩
  · rw [threeHighCrossOfRows_rows]
    simp only [Bool.and_eq_true]
    exact ⟨((mem_threeHighCrossDomain_iff UAdj RAdj cross).mp hc).2, ha⟩

end Erdos85
#print axioms Erdos85.encodedExternalBlockCap_mono
#print axioms Erdos85.threeHighExternalBlockCap_prefix

#print axioms Erdos85.threeHighExternalPrunedDFS_witness
