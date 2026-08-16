import Proofs.Erdos85OrderFortyNineThreeHighDistOneCaseTerminal
import Proofs.Erdos85OrderFortyNineThreeHighDistOneC1Normalization
import Proofs.Erdos85OrderFortyNineThreeHighDistOneC2Normalization

/-! # Complete certificate composition for the three-high stratum -/

namespace Erdos85

/-- The exact final H3 composition.  Structural normalization supplies one
aligned representative for each distinct-root case; four independently
checked LRAT payloads exclude `b1`, `c1`, `c2`, and the equal-root `dist2`
case. -/
theorem orderFortyNineStratumExcluded_three_of_distOneCovers_and_lrat
    (hb1Cover : ThreeHighDistOneB1AlignedCover)
    (b1Certificate : ThreeHighDistOneB1ScoutCertificate)
    (c1Certificate : ThreeHighDistOneC1ScoutCertificate)
    (c2Certificate : ThreeHighDistOneC2ScoutCertificate)
    (distTwoProof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (distTwoChecked : Std.Tactic.BVDecide.LRAT.check distTwoProof
      orderFortyNineGeneratedThreeHighDistTwoScoutCnf) :
    OrderFortyNineStratumExcluded 3 := by
  have hb1 : ThreeHighDistOneB1Excluded :=
    threeHighDistOneB1Excluded_of_alignedCover_lrat
      hb1Cover b1Certificate
  have hc1 : ThreeHighDistOneC1Excluded :=
    threeHighDistOneC1Excluded_of_alignedCover_lrat
      orderFortyNine_threeHighDistOneC1AlignedCover c1Certificate
  have hcover : ThreeHighDistinctRootAlignedCover :=
    threeHighDistinctRootAlignedCover_of_b1_c1_c2 hb1 hc1
      orderFortyNine_threeHighDistOneC2AlignedCover
  have hdistinct : ThreeHighDistinctRootExcluded :=
    threeHighDistinctRootExcluded_of_alignedCover hcover c2Certificate
  exact orderFortyNineStratumExcluded_three_of_distinctRoot_and_distTwo_lrat
    hdistinct distTwoProof distTwoChecked

end Erdos85
