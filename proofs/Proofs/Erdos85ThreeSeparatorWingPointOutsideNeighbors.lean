import Proofs.Erdos85ThreeSeparatorExceptionalPointWRLocation

/-!
# Exact outside neighbors of a separator-wing point

Once the wing profile supplies `q - 2` neighbors inside the large shore,
regularity leaves exactly two neighbors outside it.  Thus two known distinct
outside neighbors exhaust the outside neighborhood.
-/

open Finset SimpleGraph

namespace Erdos85

/-- A vertex of a `q`-regular graph with `q - 2` neighbors in `Y` has no
outside neighbors beyond any two distinct outside neighbors already known. -/
theorem neighborFinset_sdiff_eq_pair_of_internal_card_sub_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (q : ℕ) (hreg : ∀ v, A.degree v = q)
    (Y : Finset V) (r x w : V)
    (hq : 2 ≤ q)
    (hinternal : (A.neighborFinset r ∩ Y).card = q - 2)
    (hxY : x ∉ Y) (hwY : w ∉ Y) (hxw : x ≠ w)
    (hrx : A.Adj r x) (hrw : A.Adj r w) :
    A.neighborFinset r \ Y = {x, w} := by
  have houtCard : (A.neighborFinset r \ Y).card = 2 := by
    rw [Finset.card_sdiff]
    · rw [A.card_neighborFinset_eq_degree, hreg, Finset.inter_comm, hinternal]
      omega
  have hpairSubset : {x, w} ⊆ A.neighborFinset r \ Y := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz
    · subst z
      exact Finset.mem_sdiff.mpr ⟨(A.mem_neighborFinset r x).mpr hrx, hxY⟩
    · subst z
      exact Finset.mem_sdiff.mpr ⟨(A.mem_neighborFinset r w).mpr hrw, hwY⟩
  exact (Finset.eq_of_subset_of_card_le hpairSubset (by
    rw [houtCard]
    simp [hxw])).symm

#print axioms neighborFinset_sdiff_eq_pair_of_internal_card_sub_two

end Erdos85
