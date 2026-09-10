import Proofs.Erdos85BlockDeficitBound
import Proofs.Erdos85ThreeHighFactoredExternalDFS

namespace Erdos85

def threeHighUBlock (i : Fin 15) : Fin 3 := ((@finProdFinEquiv 3 5).symm i).1

theorem threeHighCrossBlockCap_fibers (cross : ThreeHighCross)
    (hcap : threeHighCrossBlockCap cross = true) :
    ∀ j b, ((Finset.univ.filter fun i => cross i j).filter
      fun i => threeHighUBlock i = b).card ≤ 1 := by
  unfold threeHighCrossBlockCap at hcap
  simp only [decide_eq_true_eq] at hcap
  intro j b
  let S := (Finset.univ.filter fun i => cross i j).filter fun i => threeHighUBlock i = b
  let f : Fin 15 → Fin 5 := fun i => ((@finProdFinEquiv 3 5).symm i).2
  have hb {i : Fin 15} (hi : i ∈ S) : threeHighUBlock i = b := (Finset.mem_filter.mp hi).2
  have hinj : Set.InjOn f (↑S : Set (Fin 15)) := by
    intro i hi l hl he
    apply (@finProdFinEquiv 3 5).symm.injective
    exact Prod.ext ((hb hi).trans (hb hl).symm) he
  have hsub : S.image f ⊆ Finset.univ.filter
      (fun a => cross ((@finProdFinEquiv 3 5) (b,a)) j) := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    have he : (@finProdFinEquiv 3 5) (b,f i) = i := by
      have hp : (b,f i) = (@finProdFinEquiv 3 5).symm i :=
        Prod.ext (hb hi).symm rfl
      rw [hp]
      exact Equiv.apply_symm_apply _ i
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [he]
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
  have he := Finset.card_image_iff.mpr hinj
  have h := (Finset.card_le_card hsub).trans (hcap j b)
  rwa [he] at h

attribute [local irreducible] threeHighCrossDomain

theorem threeHighExternalCap_prefix_blockCanFill
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain UAdj RAdj)
    (hExt : encodedExternalBlockCap (threeHighEmptyAdj UAdj RAdj cross) threeHighCanonicalRow = true)
    (k : Nat) :
    threeHighCrossBlockCanFill RAdj (threeHighCrossPrefix cross k) k threeHighUBlock = true := by
  rw [threeHighExternalBlockCap_factor, Bool.and_eq_true] at hExt
  exact threeHighCrossDomain_prefix_blockCanFill UAdj RAdj cross hc threeHighUBlock
    (threeHighCrossBlockCap_fibers cross hExt.2) k

/-- Count unfinished blocks rather than unfinished rows when testing column deficits. -/
def threeHighBlockDeficitDFS (UAdj : Fin 15 → Fin 15 → Bool)
    (RAdj : Fin 8 → Fin 8 → Bool) (accept : ThreeHighCross → Bool) : Bool :=
  let fixedCap := threeHighUnionBlockCap UAdj
  finiteRowDFS (threeHighRootPrunedRowList UAdj)
    (fun k rows =>
      let cross := threeHighCrossOfRows rows
      threeHighCrossCapacity RAdj cross &&
        threeHighCrossBlockCanFill RAdj cross k threeHighUBlock &&
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

theorem threeHighBlockDeficitDFS_witness
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (accept : ThreeHighCross → Bool) (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain UAdj RAdj)
    (hExt : encodedExternalBlockCap (threeHighEmptyAdj UAdj RAdj cross) threeHighCanonicalRow = true)
    (ha : accept cross = true) : threeHighBlockDeficitDFS UAdj RAdj accept = true := by
  unfold threeHighBlockDeficitDFS
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
      threeHighExternalCap_prefix_blockCanFill UAdj RAdj cross hc hExt k⟩,
      (by simpa only [Bool.and_eq_true] using he)⟩,threeHighCrossDomain_prefix_c4 UAdj RAdj cross hc k⟩
  · rw [threeHighCrossOfRows_rows]
    simp only [Bool.and_eq_true]
    exact ⟨((mem_threeHighCrossDomain_iff UAdj RAdj cross).mp hc).2,ha⟩

end Erdos85
#print axioms Erdos85.threeHighCrossBlockCap_fibers
#print axioms Erdos85.threeHighExternalCap_prefix_blockCanFill

#print axioms Erdos85.threeHighBlockDeficitDFS_witness
