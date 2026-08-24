import Proofs.Erdos85OwnerAdaptedBrokenFiberPairing
import Proofs.Erdos85PairedStarTWordGaugeParity

/-!
# Exact owner-exit residue in the `11` fiber

The owner-adapted normal form leaves one cross owner exit exactly when the
broken `11` fiber contains one special leaf.  With zero leaves there is no
owner occurrence; with two leaves they pair internally.  This identifies
the sole odd owner-cell residue left after `(73rnz_cjiba)`.
-/

namespace Erdos85

noncomputable section

/-- Special leaves paired outside the special-leaf subset. -/
def ownerExitLeaves {V : Type*} [DecidableEq V]
    (leaves : Finset V) (mate : V → V) : Finset V :=
  leaves.filter fun l => mate l ∉ leaves

/-- Exact owner-exit count for the owner-adapted broken-fiber normal form.
The output retains the full free involution and proves that its exit census
is the indicator of the one-special-leaf case. -/
theorem exists_ownerAdapted_mate_ownerExit_card_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (S leaves : Finset V) (hleaves : leaves ⊆ S)
    (heven : Even S.card) (hleTwo : leaves.card ≤ 2) :
    ∃ mate : V → V,
      (∀ v ∈ S, mate v ∈ S) ∧
      (∀ v ∈ S, mate (mate v) = v) ∧
      (∀ v ∈ S, mate v ≠ v) ∧
      (ownerExitLeaves leaves mate).card =
        if leaves.card = 1 then 1 else 0 := by
  obtain ⟨mate, hclosed, hinvol, hfree, hOne, hTwo⟩ :=
    exists_ownerAdapted_mate_of_even_with_atMostTwo_leaves
      S leaves hleaves heven hleTwo
  refine ⟨mate, hclosed, hinvol, hfree, ?_⟩
  have hcases : leaves.card = 0 ∨ leaves.card = 1 ∨ leaves.card = 2 := by omega
  rcases hcases with hzero | hone | htwo
  · have hEmpty : leaves = ∅ := Finset.card_eq_zero.mp hzero
    simp [ownerExitLeaves, hEmpty]
  · have hExitEq : ownerExitLeaves leaves mate = leaves := by
      ext l
      constructor
      · intro hl
        exact (Finset.mem_filter.mp hl).1
      · intro hl
        apply Finset.mem_filter.mpr
        refine ⟨hl, ?_⟩
        exact (Finset.mem_sdiff.mp (hOne hone l hl)).2
    rw [hExitEq, hone, if_pos rfl]
  · have hExitEmpty : ownerExitLeaves leaves mate = ∅ := by
      ext l
      simp only [ownerExitLeaves, Finset.mem_filter]
      constructor
      · intro hl
        exact (hl.2 (hTwo htwo l hl.1)).elim
      · intro hl
        simp at hl
    rw [hExitEmpty, Finset.card_empty, if_neg (by omega)]

/-- Parity form: the owner-exit census is odd exactly in the one-leaf case. -/
theorem exists_ownerAdapted_mate_ownerExit_cast_eq_leaf_cast
    {V : Type*} [Fintype V] [DecidableEq V]
    (S leaves : Finset V) (hleaves : leaves ⊆ S)
    (heven : Even S.card) (hleTwo : leaves.card ≤ 2) :
    ∃ mate : V → V,
      (∀ v ∈ S, mate v ∈ S) ∧
      (∀ v ∈ S, mate (mate v) = v) ∧
      (∀ v ∈ S, mate v ≠ v) ∧
      ((ownerExitLeaves leaves mate).card : ZMod 2) =
        (leaves.card : ZMod 2) := by
  obtain ⟨mate, hclosed, hinvol, hfree, hcard⟩ :=
    exists_ownerAdapted_mate_ownerExit_card_eq
      S leaves hleaves heven hleTwo
  refine ⟨mate, hclosed, hinvol, hfree, ?_⟩
  have hcases : leaves.card = 0 ∨ leaves.card = 1 ∨ leaves.card = 2 := by omega
  rcases hcases with hzero | hone | htwo
  · rw [hcard, hzero]
    norm_num
  · rw [hcard, hone]
    norm_num
  · rw [hcard, htwo]
    have htwoZ : (2 : ZMod 2) = 0 := by decide
    exact htwoZ.symm

end

end Erdos85

#print axioms Erdos85.exists_ownerAdapted_mate_ownerExit_card_eq
#print axioms Erdos85.exists_ownerAdapted_mate_ownerExit_cast_eq_leaf_cast
