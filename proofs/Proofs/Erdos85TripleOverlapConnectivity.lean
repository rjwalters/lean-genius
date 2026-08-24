import Proofs.Erdos85ConnectedF2EdgeSwitchSpan

/-!
# Connectivity of the triple-overlap graph

The complete-fiber Baer switch argument indexes elementary triangle
decompositions by three-element subsets.  Two decompositions differ by a
quadrilateral switch when their triples share two labels.  This file proves
that this overlap graph is connected and instantiates the general binary
edge-switch span theorem.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Three-element subsets of a finite label type. -/
abbrev TripleSubset (U : Type*) := {s : Finset U // s.card = 3}

/-- The graph in which two triples are adjacent exactly when their
intersection has two elements. -/
def tripleOverlapGraph (U : Type*) [DecidableEq U] :
    SimpleGraph (TripleSubset U) where
  Adj S T := (S.1 ∩ T.1).card = 2
  symm := by
    constructor
    intro S T h
    simpa [Finset.inter_comm] using h
  loopless := by
    constructor
    intro S h
    rw [Finset.inter_self, S.2] at h
    omega

private theorem tripleOverlapGraph_preconnected
    (U : Type*) [Fintype U] [DecidableEq U] :
    (tripleOverlapGraph U).Preconnected := by
  intro S T
  rw [SimpleGraph.reachable_iff_reflTransGen]
  induction hdelta : (S.1 \ T.1).card using Nat.strong_induction_on generalizing S with
  | h n ih =>
      by_cases hST : S = T
      · subst T
        exact Relation.ReflTransGen.refl
      · have hdiffST : (S.1 \ T.1).Nonempty := by
          rw [Finset.sdiff_nonempty]
          intro hsub
          apply hST
          apply Subtype.ext
          exact Finset.eq_of_subset_of_card_le hsub (by simp [S.2, T.2])
        have hdiffTS : (T.1 \ S.1).Nonempty := by
          rw [Finset.sdiff_nonempty]
          intro hsub
          apply hST
          apply Subtype.ext
          exact (Finset.eq_of_subset_of_card_le hsub (by simp [S.2, T.2])).symm
        obtain ⟨a, ha⟩ := hdiffST
        obtain ⟨b, hb⟩ := hdiffTS
        have ⟨haS, haT⟩ := Finset.mem_sdiff.mp ha
        have ⟨hbT, hbS⟩ := Finset.mem_sdiff.mp hb
        let S' : TripleSubset U :=
          ⟨insert b (S.1.erase a), by simp [haS, hbS, S.2]⟩
        have hadj : (tripleOverlapGraph U).Adj S S' := by
          simp only [tripleOverlapGraph, S']
          simp only [Finset.inter_insert_of_notMem hbS]
          rw [Finset.inter_eq_right.mpr (Finset.erase_subset _ _),
            Finset.card_erase_of_mem haS, S.2]
        have hlt : (S'.1 \ T.1).card < n := by
          rw [← hdelta]
          change ((insert b (S.1.erase a)) \ T.1).card < (S.1 \ T.1).card
          calc
            ((insert b (S.1.erase a)) \ T.1).card =
                ((S.1 \ T.1).erase a).card := by
                  congr 1
                  ext x
                  simp only [Finset.mem_sdiff, Finset.mem_insert,
                    Finset.mem_erase]
                  aesop
            _ < (S.1 \ T.1).card :=
              Finset.card_erase_lt_of_mem (Finset.mem_sdiff.mpr ⟨haS, haT⟩)
        exact Relation.ReflTransGen.head hadj (ih _ hlt S' rfl)

/-- The graph of triples joined by two-point overlap is connected whenever
the ground type contains at least one triple. -/
theorem tripleOverlapGraph_connected
    (U : Type*) [Fintype U] [DecidableEq U]
    (hne : Nonempty (TripleSubset U)) :
    (tripleOverlapGraph U).Connected := by
  letI : Nonempty (TripleSubset U) := hne
  exact ⟨tripleOverlapGraph_preconnected U⟩

/-- Quadrilateral switches between overlapping triples generate precisely
the even binary coefficient vectors on triples. -/
theorem tripleOverlapSwitches_span_eq_coordinateSum_ker
    (U : Type*) [Fintype U] [DecidableEq U]
    (hne : Nonempty (TripleSubset U)) :
    Submodule.span (ZMod 2) (f2GraphEdgeSwitches (tripleOverlapGraph U)) =
      LinearMap.ker (f2CoordinateSum (TripleSubset U)) :=
  f2GraphEdgeSwitches_span_eq_coordinateSum_ker _
    (tripleOverlapGraph_connected U hne)

end

end Erdos85

#print axioms Erdos85.tripleOverlapGraph_connected
#print axioms Erdos85.tripleOverlapSwitches_span_eq_coordinateSum_ker
