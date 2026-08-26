import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalCnfSatisfaction

/-!
# C4 witnesses for the compact canonical H7/T0 clauses

The generated C4 segment forbids the four cross edges between two distinct
endpoints and two distinct witnesses.  This file isolates the graph-theoretic
kernel fact used to satisfy every such clause.
-/

namespace Erdos85

open SimpleGraph

/-- In a C4-free graph, two distinct endpoints and two distinct witnesses
cannot carry all four cross adjacencies. -/
theorem sevenHighT0Canonical_fourCross_not_all_adj
    {H : SimpleGraph SevenHighT0CanonicalIndex}
    [DecidableRel H.Adj]
    (hfree : ¬ containsC4 SevenHighT0CanonicalIndex H)
    {left right first second : SevenHighT0CanonicalIndex}
    (hlr : left ≠ right) (hfs : first ≠ second) :
    ¬ (H.Adj left first ∧ H.Adj right first ∧
      H.Adj left second ∧ H.Adj right second) := by
  rintro ⟨hlf, hrf, hls, hrs⟩
  have hle :=
    (not_containsC4_iff_forall_common_le_one H).mp hfree left right hlr
  have hfirst : first ∈ H.neighborFinset left ∩ H.neighborFinset right := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hlf, hrf⟩
  have hsecond : second ∈ H.neighborFinset left ∩ H.neighborFinset right := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hls, hrs⟩
  exact hfs (Finset.card_le_one.mp hle first hfirst second hsecond)

/-- Clause-shaped disjunctive form: at least one of the four cross edges is
absent. -/
theorem sevenHighT0Canonical_exists_missing_cross_edge
    {H : SimpleGraph SevenHighT0CanonicalIndex}
    [DecidableRel H.Adj]
    (hfree : ¬ containsC4 SevenHighT0CanonicalIndex H)
    {left right first second : SevenHighT0CanonicalIndex}
    (hlr : left ≠ right) (hfs : first ≠ second) :
    ¬ H.Adj left first ∨ ¬ H.Adj right first ∨
      ¬ H.Adj left second ∨ ¬ H.Adj right second := by
  by_contra hall
  simp only [not_or, not_not] at hall
  exact sevenHighT0Canonical_fourCross_not_all_adj hfree hlr hfs
    ⟨hall.1, hall.2.1, hall.2.2.1, hall.2.2.2⟩

/-- The semantic completion package supplies the same clause witness. -/
theorem SevenHighT0CanonicalCompletionSemantics.exists_missing_cross_edge
    {H : SimpleGraph SevenHighT0CanonicalIndex}
    [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H)
    {left right first second : SevenHighT0CanonicalIndex}
    (hlr : left ≠ right) (hfs : first ≠ second) :
    ¬ H.Adj left first ∨ ¬ H.Adj right first ∨
      ¬ H.Adj left second ∨ ¬ H.Adj right second :=
  sevenHighT0Canonical_exists_missing_cross_edge
    semantics.c4Free hlr hfs

end Erdos85

#print axioms Erdos85.sevenHighT0Canonical_fourCross_not_all_adj
#print axioms Erdos85.SevenHighT0CanonicalCompletionSemantics.exists_missing_cross_edge
