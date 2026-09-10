import Proofs.Erdos85ThreeHighCrossDeficit

namespace Erdos85

/-- A neighbor set with at most one point per block cannot fill more than one
remaining slot per unfinished block. -/
theorem card_le_assigned_add_unfinished_blocks
    {V K : Type*} [Fintype V] [DecidableEq V] [DecidableEq K]
    (S assigned : Finset V) (block : V → K)
    (hcap : ∀ k, (S.filter fun x => block x = k).card ≤ 1) :
    S.card ≤ (S ∩ assigned).card + ((Finset.univ \ assigned).image block).card := by
  have hinj : Set.InjOn block (↑(S \ assigned) : Set V) := by
    intro a ha b hb hab
    have haS := (Finset.mem_sdiff.mp ha).1
    have hbS := (Finset.mem_sdiff.mp hb).1
    exact Finset.card_le_one.mp (hcap (block a)) a
      (Finset.mem_filter.mpr ⟨haS,rfl⟩) b
      (Finset.mem_filter.mpr ⟨hbS,hab.symm⟩)
  have he : ((S \ assigned).image block).card = (S \ assigned).card :=
    Finset.card_image_iff.mpr hinj
  have hs : (S \ assigned).image block ⊆ (Finset.univ \ assigned).image block := by
    apply Finset.image_subset_image
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x,(Finset.mem_sdiff.mp hx).2⟩
  have hc := Finset.card_le_card hs
  rw [he] at hc
  have hsplit := Finset.card_sdiff_add_card_inter S assigned
  omega

def threeHighCrossBlockCanFill (RAdj : Fin 8 → Fin 8 → Bool)
    (partialCross : ThreeHighCross) (k : Nat) (block : Fin 15 → Fin 3) : Bool :=
  decide (∀ j, 4 ≤ encodedRowDegree (fun i => partialCross i j) +
    encodedRowDegree (RAdj j) + (if j.val < 6 then 1 else 0) +
      ((threeHighUnassignedRows k).image block).card)

theorem threeHighCrossPrefix_block_bound (cross : ThreeHighCross) (k : Nat)
    (block : Fin 15 → Fin 3) (j : Fin 8)
    (hcap : ∀ b, ((Finset.univ.filter fun i => cross i j).filter
      fun i => block i = b).card ≤ 1) :
    encodedRowDegree (fun i => cross i j) ≤
      encodedRowDegree (fun i => threeHighCrossPrefix cross k i j) +
        ((threeHighUnassignedRows k).image block).card := by
  let assigned : Finset (Fin 15) := Finset.univ.filter fun i => i.val < k
  have hinter : (Finset.univ.filter fun i => cross i j) ∩ assigned =
      Finset.univ.filter (fun i => threeHighCrossPrefix cross k i j) := by
    ext i
    by_cases hi : i.val < k <;> simp [assigned,threeHighCrossPrefix,hi]
  have hun : Finset.univ \ assigned = threeHighUnassignedRows k := by
    ext i
    simp [assigned,threeHighUnassignedRows,not_lt]
  have h := card_le_assigned_add_unfinished_blocks
    (Finset.univ.filter fun i => cross i j) assigned block hcap
  simpa only [encodedRowDegree,hinter,hun] using h

attribute [local irreducible] threeHighCrossDomain

theorem threeHighCrossDomain_prefix_blockCanFill
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain UAdj RAdj)
    (block : Fin 15 → Fin 3)
    (hcap : ∀ j b, ((Finset.univ.filter fun i => cross i j).filter
      fun i => block i = b).card ≤ 1) (k : Nat) :
    threeHighCrossBlockCanFill RAdj (threeHighCrossPrefix cross k) k block = true := by
  simp only [threeHighCrossBlockCanFill,decide_eq_true_eq]
  intro j
  have hm := (threeHighCrossDomain_margins UAdj RAdj cross hc).2 j
  have hb := threeHighCrossPrefix_block_bound cross k block j (hcap j)
  omega

end Erdos85
#print axioms Erdos85.card_le_assigned_add_unfinished_blocks

#print axioms Erdos85.threeHighCrossPrefix_block_bound
#print axioms Erdos85.threeHighCrossDomain_prefix_blockCanFill
