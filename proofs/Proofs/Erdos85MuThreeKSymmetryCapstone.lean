import Proofs.Erdos85MuThreeMixedGridKSymmetry

/-!
# A uniform K-symmetry enumeration capstone

This module is the interface between the graph-facing mixed-grid reduction
and the finite computations used to close each internal shape/sector.

An enumeration provider proves that every two-regular, cycle-compatible `K`
satisfying the row and column symmetry laws is one of a Boolean-indexed list
of candidates.  A certificate provider refutes `MuThreeMixedGridCode` for
each candidate.  The capstone combines the two directly on the *actual*
mixed-grid code; it does not expose a normalized `Fin 8` relation to its
caller.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The structural data about `K` which the finite enumeration may use.
Every field follows from an actual `MuThreeMixedGridCode`; in particular the
last two fields are the K-symmetry law. -/
structure MuThreeKSymmetryData
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K] : Prop where
  card_left : Fintype.card X = 8
  card_right : Fintype.card Y = 8
  H_twoRegular : RelationTwoRegular H
  K_twoRegular : RelationTwoRegular K
  cycle_compatible : RelationFactorCycleCompatible H K
  row_symmetry : ∀ x x',
    Fintype.card {y : Y // H x' y ∧ ¬ K x y} =
      Fintype.card {y : Y // H x y ∧ ¬ K x' y}
  column_symmetry : ∀ y y',
    Fintype.card {x : X // H x y' ∧ ¬ K x y} =
      Fintype.card {x : X // H x y ∧ ¬ K x y'}

/-- The symmetry data extracted from the actual exterior grid code. -/
def MuThreeMixedGridCode.kSymmetryData
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) :
    MuThreeKSymmetryData H K where
  card_left := code.card_left
  card_right := code.card_right
  H_twoRegular := code.H_twoRegular
  K_twoRegular := code.K_twoRegular
  cycle_compatible := code.cycle_compatible
  row_symmetry := code.card_H_and_not_K_row_symm H K C
  column_symmetry := code.card_H_and_not_K_column_symm H K C

/-- Turn a Boolean candidate table into the relation it represents. -/
def muThreeKCandidateRel
    {X Y I : Type*} (candidate : I → X → Y → Bool) (i : I) :
    X → Y → Prop := fun x y => candidate i x y = true

instance muThreeKCandidateRel_decidable
    {X Y I : Type*} (candidate : I → X → Y → Bool) (i : I) :
    DecidableRel (muThreeKCandidateRel candidate i) := by
  intro x y
  unfold muThreeKCandidateRel
  infer_instance

/-- Contract shared by the enumeration and fixed-K certificate providers.

`exhaustive` is the (shape/sector-specific) finite enumeration theorem.
`impossible` is supplied by the checked fixed-K certificates.  The index type
may be `Fin n`; it is intentionally not required to be finite by the abstract
capstone itself. -/
structure MuThreeKSymmetryClassification
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H : X → Y → Prop) [DecidableRel H] where
  Index : Type*
  candidate : Index → X → Y → Bool
  exhaustive : ∀ (K : X → Y → Prop) [DecidableRel K],
    MuThreeKSymmetryData H K →
      ∃ i : Index, ∀ x y, K x y ↔ muThreeKCandidateRel candidate i x y
  impossible : ∀ (i : Index)
    (dK : DecidableRel (muThreeKCandidateRel candidate i))
    (C : SimpleGraph (muThreeMixedCell (muThreeKCandidateRel candidate i)))
    [dC : DecidableRel C.Adj],
    ¬ @MuThreeMixedGridCode X Y _ _ _ _ H
      (muThreeKCandidateRel candidate i) _ dK C dC

/-- **Uniform K-symmetry capstone.**  Enumeration plus one impossibility
certificate for every enumerated `K` rules out the actual mixed-grid code.

This is the graph-facing socket: its conclusion quantifies over the original
`X`, `Y`, `H`, `K`, and exterior graph `C`.  Coordinate relabeling is confined
to the construction of `classification`. -/
theorem false_of_muThreeMixedGridCode_of_kSymmetryClassification
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [dH : DecidableRel H] [dK : DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [dC : DecidableRel C.Adj]
    (classification : MuThreeKSymmetryClassification H)
    (code : MuThreeMixedGridCode H K C) : False := by
  obtain ⟨i, hi⟩ := classification.exhaustive K (code.kSymmetryData H K C)
  have hK : K = muThreeKCandidateRel classification.candidate i := by
    funext x y
    exact propext (hi x y)
  subst K
  exact classification.impossible i dK C code

end


end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.kSymmetryData
#print axioms Erdos85.false_of_muThreeMixedGridCode_of_kSymmetryClassification
