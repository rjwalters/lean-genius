import Proofs.Erdos85SizeTwoEigenlineCyclicPermutationLoopless
import Proofs.Erdos85SizeTwoEigenlineCyclicPermutationInvolution

/-!
# Reconstructing the exterior graph from a reciprocal permutation code

Each admissible route dart determines a directed cell edge.  Reciprocity
makes this relation symmetric, while the retained loopless law makes it
irreflexive.  Hence it reconstructs a genuine simple graph.
-/

namespace Erdos85

noncomputable section

/-- The directed cell relation obtained by following one route of the code. -/
def sizeTwoCyclicCodeRouteRel
    (q : ℕ) [NeZero q] (a : ZMod q)
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (u v : sizeTwoCyclicExteriorCell q a) : Prop :=
  let z := sizeTwoCyclicExteriorCellEquiv q a u
  ∃ r : SizeTwoAdmissibleTargetRow q z.2.1,
    v = sizeTwoCyclicCellAt q a (z.1 + r.1)
      (code.targetDifference z.1 z.2 r)

/-- Reciprocity makes the directed route relation symmetric. -/
theorem sizeTwoCyclicCodeRouteRel_symm
    (q : ℕ) [NeZero q] (a : ZMod q)
    (code : SizeTwoCyclicReciprocalPermutationCode q a) :
    Symmetric (sizeTwoCyclicCodeRouteRel q a code) := by
  intro u v huv
  unfold sizeTwoCyclicCodeRouteRel at huv ⊢
  let z := sizeTwoCyclicExteriorCellEquiv q a u
  change ∃ r : SizeTwoAdmissibleTargetRow q z.2.1,
    v = sizeTwoCyclicCellAt q a (z.1 + r.1)
      (code.targetDifference z.1 z.2 r) at huv
  obtain ⟨r, rfl⟩ := huv
  let s := code.targetDifference z.1 z.2 r
  let reverseRow : SizeTwoAdmissibleTargetRow q s.1 :=
    ⟨-r.1, code.reverse_admissible z.1 z.2 r⟩
  rw [sizeTwoCyclicExteriorCellEquiv_cellAt]
  change ∃ r' : SizeTwoAdmissibleTargetRow q s.1,
    u = sizeTwoCyclicCellAt q a (z.1 + r.1 + r'.1)
      (code.targetDifference (z.1 + r.1) s r')
  refine ⟨reverseRow, ?_⟩
  rw [code.reverse_targetDifference z.1 z.2 r]
  have hu : u = sizeTwoCyclicCellAt q a z.1 z.2 := by
    apply (sizeTwoCyclicExteriorCellEquiv q a).injective
    simp [z]
  rw [hu]
  apply (sizeTwoCyclicExteriorCellEquiv q a).injective
  simp [reverseRow]

/-- The loopless code law makes the route relation irreflexive. -/
theorem sizeTwoCyclicCodeRouteRel_irrefl
    (q : ℕ) [NeZero q] (a : ZMod q)
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (hloop : code.Loopless) :
    Irreflexive (sizeTwoCyclicCodeRouteRel q a code) := by
  intro u huu
  unfold sizeTwoCyclicCodeRouteRel at huu
  let z := sizeTwoCyclicExteriorCellEquiv q a u
  change ∃ r : SizeTwoAdmissibleTargetRow q z.2.1,
    u = sizeTwoCyclicCellAt q a (z.1 + r.1)
      (code.targetDifference z.1 z.2 r) at huu
  obtain ⟨r, heq⟩ := huu
  apply hloop z.1 z.2 r
  have hc := congrArg (sizeTwoCyclicExteriorCellEquiv q a) heq
  have hbase : r.1 = 0 := by
    have := congrArg Prod.fst hc
    simp [z] at this
    apply add_left_cancel (a := z.1)
    simpa using this
  have hdiff : code.targetDifference z.1 z.2 r = z.2 := by
    apply Subtype.ext
    have := congrArg (fun p => p.2.1) hc
    simpa [z] using this.symm
  exact ⟨hbase, hdiff⟩

/-- The simple graph reconstructed from the route relation. -/
def sizeTwoCyclicCodeGraph
    (q : ℕ) [NeZero q] (a : ZMod q)
    (code : SizeTwoCyclicReciprocalPermutationCode q a) :
    SimpleGraph (sizeTwoCyclicExteriorCell q a) :=
  SimpleGraph.fromRel (sizeTwoCyclicCodeRouteRel q a code)

/-- Under looplessness, reconstructed adjacency is exactly the route relation
(the symmetrization in `fromRel` adds nothing). -/
theorem sizeTwoCyclicCodeGraph_adj_iff
    (q : ℕ) [NeZero q] (a : ZMod q)
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (hloop : code.Loopless)
    (u v : sizeTwoCyclicExteriorCell q a) :
    (sizeTwoCyclicCodeGraph q a code).Adj u v ↔
      sizeTwoCyclicCodeRouteRel q a code u v := by
  rw [sizeTwoCyclicCodeGraph, SimpleGraph.fromRel_adj]
  have hsymm := sizeTwoCyclicCodeRouteRel_symm q a code
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact hsymm h
  · intro h
    exact ⟨fun huv =>
      (sizeTwoCyclicCodeRouteRel_irrefl q a code hloop u) (huv ▸ h), Or.inl h⟩

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicCodeRouteRel_symm
#print axioms Erdos85.sizeTwoCyclicCodeRouteRel_irrefl
#print axioms Erdos85.sizeTwoCyclicCodeGraph_adj_iff
