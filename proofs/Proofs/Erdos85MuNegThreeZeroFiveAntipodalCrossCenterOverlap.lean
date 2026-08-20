import Proofs.Erdos85MuNegThreeZeroFiveAntipodalForcedCover

/-! # Routing residual positive-shore targets to another antipodal center -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Every type-one edge is in the global antipodal forced cover.  Therefore,
if it is outside the forced set of one center, it lies in the forced set of
a genuinely different coordinate center. -/
theorem h305_typeOne_outside_antipodalStar_forced_by_other_coordinate
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u : ZMod 8 → V) (i : ZMod 8)
    (e : R.edgeFinset)
    (heType : e ∈ shoreTypeEdgeFinset R
      ((Finset.univ : Finset (ZMod 8)).image u) 1)
    (heOutside : e.1 ∉ h305AntipodalSaturatedStarUnion R u i) :
    ∃ j : ZMod 8, j ≠ i ∧
      e.1 ∈ h305AntipodalSaturatedStarUnion R u j := by
  classical
  let U := (Finset.univ : Finset (ZMod 8)).image u
  let eR : R.edgeFinset ↪ Sym2 V := Function.Embedding.subtype _
  have hePositive : e.1 ∈
      ((shoreTypeEdgeFinset R U 1) ∪
        shoreTypeEdgeFinset R U 2).map eR := by
    apply Finset.mem_map.mpr
    exact ⟨e, Finset.mem_union.mpr (Or.inl (by simpa [U] using heType)), rfl⟩
  have heCover : e.1 ∈ h305AntipodalForcedCover R u := by
    rw [h305_antipodalForcedCover_eq_positiveShoreTypes R u]
    exact hePositive
  obtain ⟨j, _, hej⟩ := Finset.mem_biUnion.mp heCover
  refine ⟨j, ?_, hej⟩
  intro hji
  subst j
  exact heOutside hej

end

end Erdos85

#print axioms
  Erdos85.h305_typeOne_outside_antipodalStar_forced_by_other_coordinate
