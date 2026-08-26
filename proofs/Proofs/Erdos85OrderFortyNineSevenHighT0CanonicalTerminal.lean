import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalSemantics
import Proofs.Erdos85OrderFortyNineSevenHighCertificates
import Proofs.Erdos85OrderFortyNineSevenHighGraphCover

/-!
# Canonical H7/T0 UNSAT socket and seven-high assembly

This file connects the new canonical completion semantics directly to the
existing graph stratum hierarchy.  A checked proof that no canonical
completion graph exists closes the `t=0` triple cell; the already checked
certificates close cells `t=1,...,7`.
-/

namespace Erdos85

open SimpleGraph

def SevenHighT0CanonicalCompletionExcluded : Prop :=
  ∀ (H : SimpleGraph SevenHighT0CanonicalIndex) (_ : DecidableRel H.Adj),
    SevenHighT0CanonicalCompletionSemantics H → False

/-- Semantic UNSAT for the canonical completion model directly excludes the
actual seven-high, zero-triple graph cell. -/
theorem orderFortyNineTripleCellExcluded_seven_zero_of_canonicalCompletion
    (hexcluded : SevenHighT0CanonicalCompletionExcluded) :
    OrderFortyNineTripleCellExcluded 7 0 := by
  intro G _ _ _ hfree hmin hHigh hzero
  let e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7 :=
    Fintype.equivFinOfCardEq (by simpa using hHigh)
  exact hexcluded
    (sevenHighT0CanonicalGraph G hfree hmin hHigh hzero e)
    inferInstance
    (sevenHighT0CanonicalGraph_completionSemantics
      G hfree hmin hHigh hzero e)

/-- The canonical H7/T0 completion exclusion plus the thirteen already
checked positive-triple certificates excludes the entire seven-high stratum. -/
theorem orderFortyNineStratumExcluded_seven_of_canonicalCompletion
    (hexcluded : SevenHighT0CanonicalCompletionExcluded) :
    OrderFortyNineStratumExcluded 7 := by
  apply orderFortyNineStratumExcluded_seven_of_tripleCells
  · exact orderFortyNineTripleCellExcluded_seven_zero_of_canonicalCompletion
      hexcluded
  · apply orderFortyNineTripleCellExcluded_seven_of_canonical
      (sevenHighCanonicalGraphCover_all 1 (by omega))
    intro index hindex
    simp [OrderFortyNineSevenHighCensus.reps] at hindex
    have : index = 0 := by omega
    subst index
    exact sevenHighT1Rep0_excluded
  · apply orderFortyNineTripleCellExcluded_seven_of_canonical
      (sevenHighCanonicalGraphCover_all 2 (by omega))
    intro index hindex
    simp [OrderFortyNineSevenHighCensus.reps] at hindex
    interval_cases index
    · exact sevenHighT2Rep0_excluded
    · exact sevenHighT2Rep1_excluded
  · apply orderFortyNineTripleCellExcluded_seven_of_canonical
      (sevenHighCanonicalGraphCover_all 3 (by omega))
    intro index hindex
    simp [OrderFortyNineSevenHighCensus.reps] at hindex
    interval_cases index
    · exact sevenHighT3Rep0_excluded
    · exact sevenHighT3Rep1_excluded
    · exact sevenHighT3Rep2_excluded
  · apply orderFortyNineTripleCellExcluded_seven_of_canonical
      (sevenHighCanonicalGraphCover_all 4 (by omega))
    intro index hindex
    simp [OrderFortyNineSevenHighCensus.reps] at hindex
    interval_cases index
    · exact sevenHighT4Rep0_excluded
    · exact sevenHighT4Rep1_excluded
    · exact sevenHighT4Rep2_excluded
  · apply orderFortyNineTripleCellExcluded_seven_of_canonical
      (sevenHighCanonicalGraphCover_all 5 (by omega))
    intro index hindex
    simp [OrderFortyNineSevenHighCensus.reps] at hindex
    interval_cases index
    · exact sevenHighT5Rep0_excluded
    · exact sevenHighT5Rep1_excluded
  · apply orderFortyNineTripleCellExcluded_seven_of_canonical
      (sevenHighCanonicalGraphCover_all 6 (by omega))
    intro index hindex
    simp [OrderFortyNineSevenHighCensus.reps] at hindex
    have : index = 0 := by omega
    subst index
    exact sevenHighT6Rep0_excluded
  · apply orderFortyNineTripleCellExcluded_seven_of_canonical
      (sevenHighCanonicalGraphCover_all 7 (by omega))
    intro index hindex
    simp [OrderFortyNineSevenHighCensus.reps] at hindex
    have : index = 0 := by omega
    subst index
    exact sevenHighT7Rep0_excluded

end Erdos85

#print axioms Erdos85.orderFortyNineTripleCellExcluded_seven_zero_of_canonicalCompletion
#print axioms Erdos85.orderFortyNineStratumExcluded_seven_of_canonicalCompletion
