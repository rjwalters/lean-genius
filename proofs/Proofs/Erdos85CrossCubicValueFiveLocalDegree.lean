import Proofs.Erdos85CubicEqualityMarkedEdgeMatching
import Proofs.Erdos85CubicDiagonalParity

/-! # From local value-five matchings to global marked degree -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- A diagonal cubic walk count cannot be five.  Reversing the walk is not
enough on the diagonal; the standard oriented-triangle parity gives the
required loop exclusion. -/
theorem residualFiberCubicWalkCount_self_ne_five
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (a : R.edgeFinset) :
    residualFiberCubicWalkCount R Cedge a a ≠ 5 := by
  intro hfive
  have hwalk := Cedge.adjMatrix_pow_apply_eq_card_walk
    (α := ℤ) 3 a a
  have heq :
      ((residualFiberCubicWalkCount R Cedge a a : ℕ) : ℤ) =
        (Cedge.adjMatrix ℤ * Cedge.adjMatrix ℤ *
          Cedge.adjMatrix ℤ) a a := by
    simpa [residualFiberCubicWalkCount, pow_succ] using hwalk.symm
  have heven := even_adjMatrix_cube_apply_self Cedge a
  rcases heven with ⟨k, hk⟩
  rw [hfive] at heq
  omega

set_option maxHeartbeats 800000 in
/-- A two-edge local value-five matching contained in a global target set is
exactly the two-neighbor fiber of the global marked graph. -/
theorem crossTarget_markedNeighbor_card_two_of_localMatching
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (S : Finset R.edgeFinset) (a : R.edgeFinset)
    (hcard : (cubicValueFiveEdgeFinset R Cedge a).card = 2)
    (hsub : cubicValueFiveEdgeFinset R Cedge a ⊆ S) :
    (S.filter (fun b : R.edgeFinset ↦ a ≠ b ∧
      residualFiberCubicWalkCount R Cedge a b = 5)).card = 2 := by
  classical
  have heq :
      S.filter (fun b : R.edgeFinset ↦ a ≠ b ∧
        residualFiberCubicWalkCount R Cedge a b = 5) =
      cubicValueFiveEdgeFinset R Cedge a := by
    ext b
    constructor
    · intro hb
      have hb' := Finset.mem_filter.mp hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb'.2.2⟩
    · intro hb
      have hb5 := (Finset.mem_filter.mp hb).2
      exact Finset.mem_filter.mpr
        ⟨hsub hb, fun hab ↦
          residualFiberCubicWalkCount_self_ne_five R Cedge a
            (hab ▸ hb5), hb5⟩
  rw [heq, hcard]

end

end Erdos85

#print axioms Erdos85.residualFiberCubicWalkCount_self_ne_five
#print axioms Erdos85.crossTarget_markedNeighbor_card_two_of_localMatching
