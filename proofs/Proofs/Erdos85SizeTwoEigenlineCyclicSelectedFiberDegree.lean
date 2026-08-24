import Proofs.Erdos85SizeTwoEigenlineCyclicSelectedFiberGraph
import Proofs.Erdos85SizeTwoEigenlineCyclicDisplacementMultiplicityMoment

/-!
# Degrees in a selected cyclic difference fibre

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

The diagonal target-difference multiplicity at a base is exactly the degree
of that base in the graph carried by the selected difference fibre.  This
connects multiplicity classifications to the existing one-fibre `C4` cap.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Neighbours in a selected fibre are equivalent to the admissible local
rows whose target difference returns to that fibre. -/
noncomputable def sizeTwoCyclicSelectedFiberNeighborEquiv
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (hloop : code.Loopless)
    (t : sizeTwoAllowedDifference q a) (x : ZMod q)
    [DecidableRel (sizeTwoCyclicSelectedFiberGraph code t).Adj] :
    {y : ZMod q // y ∈
      (sizeTwoCyclicSelectedFiberGraph code t).neighborFinset x} ≃
    {r : SizeTwoAdmissibleTargetRow q t.1 //
      code.targetDifference x t r = t} := by
  classical
  let G := sizeTwoCyclicSelectedFiberGraph code t
  let route (y : {y : ZMod q // y ∈ G.neighborFinset x}) :=
    Classical.choose ((sizeTwoCyclicSelectedFiberGraph_adj_iff
      code hloop t x y.1).mp ((G.mem_neighborFinset x y.1).mp y.2))
  have route_spec (y : {y : ZMod q // y ∈ G.neighborFinset x}) :
      y.1 = x + (route y).1 ∧ code.targetDifference x t (route y) = t :=
    Classical.choose_spec ((sizeTwoCyclicSelectedFiberGraph_adj_iff
      code hloop t x y.1).mp ((G.mem_neighborFinset x y.1).mp y.2))
  refine
    { toFun := fun y => ⟨route y, (route_spec y).2⟩
      invFun := fun r => ⟨x + r.1.1, (G.mem_neighborFinset x _).mpr
        ((sizeTwoCyclicSelectedFiberGraph_adj_iff
          code hloop t x (x + r.1.1)).mpr ⟨r.1, rfl, r.2⟩)⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro y
    apply Subtype.ext
    exact (route_spec y).1.symm
  · intro r
    apply Subtype.ext
    apply Subtype.ext
    have hroute := (route_spec
      (⟨x + r.1.1, (G.mem_neighborFinset x _).mpr
        ((sizeTwoCyclicSelectedFiberGraph_adj_iff
          code hloop t x (x + r.1.1)).mpr ⟨r.1, rfl, r.2⟩)⟩ :
        {y : ZMod q // y ∈ G.neighborFinset x})).1
    exact add_left_cancel hroute.symm

/-- The selected-fibre degree is the diagonal local multiplicity. -/
theorem sizeTwoCyclicSelectedFiberGraph_degree_eq_diagonalMultiplicity
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (hloop : code.Loopless)
    (t : sizeTwoAllowedDifference q a) (x : ZMod q)
    [DecidableRel (sizeTwoCyclicSelectedFiberGraph code t).Adj] :
    ((sizeTwoCyclicSelectedFiberGraph code t).neighborFinset x).card =
      sizeTwoCyclicTargetDifferenceMultiplicity code x t t := by
  classical
  let G := sizeTwoCyclicSelectedFiberGraph code t
  calc
    (G.neighborFinset x).card = Fintype.card
        {y : ZMod q // y ∈ G.neighborFinset x} := by
      rw [Fintype.card_coe]
    _ = Fintype.card {r : SizeTwoAdmissibleTargetRow q t.1 //
          code.targetDifference x t r = t} :=
      Fintype.card_congr
        (sizeTwoCyclicSelectedFiberNeighborEquiv code hloop t x)
    _ = ((Finset.univ : Finset (SizeTwoAdmissibleTargetRow q t.1)).filter
          fun r => code.targetDifference x t r = t).card := by
      simpa using (Fintype.card_coe
        ((Finset.univ : Finset (SizeTwoAdmissibleTargetRow q t.1)).filter
          fun r => code.targetDifference x t r = t))
    _ = sizeTwoCyclicTargetDifferenceMultiplicity code x t t := rfl

end

end Erdos85

#print axioms
  Erdos85.sizeTwoCyclicSelectedFiberGraph_degree_eq_diagonalMultiplicity
