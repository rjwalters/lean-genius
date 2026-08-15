import Proofs.Erdos85OrderFortyNineSevenHighT1Rep0Certificate
import Proofs.Erdos85OrderFortyNineSevenHighT2Rep0Certificate
import Proofs.Erdos85OrderFortyNineSevenHighT2Rep1Certificate
import Proofs.Erdos85OrderFortyNineSevenHighT3Rep0Certificate
import Proofs.Erdos85OrderFortyNineSevenHighT3Rep1Certificate
import Proofs.Erdos85OrderFortyNineSevenHighT3Rep2Certificate
import Proofs.Erdos85OrderFortyNineSevenHighT4Rep0Certificate
import Proofs.Erdos85OrderFortyNineSevenHighT4Rep1Certificate
import Proofs.Erdos85OrderFortyNineSevenHighT4Rep2Certificate
import Proofs.Erdos85OrderFortyNineSevenHighT5Rep0Certificate
import Proofs.Erdos85OrderFortyNineSevenHighT5Rep1Certificate
import Proofs.Erdos85OrderFortyNineSevenHighT6Rep0Certificate
import Proofs.Erdos85OrderFortyNineSevenHighT7Rep0Certificate

/-!
# Aggregate checked certificates for the seven-high stratum

The twelve canonical representatives with two through seven high triples are
discharged by packed LRAT certificates.  Supplying the remaining `t = 0` and
`t = 1` exclusions closes the complete seven-high graph stratum.
-/

namespace Erdos85

theorem orderFortyNineStratumExcluded_seven_of_t0_t1
    (hzero : SevenHighCanonicalRepresentativeExcluded 0 0)
    (hone : SevenHighCanonicalRepresentativeExcluded 1 0) :
    OrderFortyNineStratumExcluded 7 := by
  apply orderFortyNineStratumExcluded_seven_of_certificates
  intro blocks index hblocks hindex
  interval_cases blocks
  · simp [OrderFortyNineSevenHighCensus.reps] at hindex
    have hi : index = 0 := by omega
    subst index
    exact hzero
  · simp [OrderFortyNineSevenHighCensus.reps] at hindex
    have hi : index = 0 := by omega
    subst index
    exact hone
  · simp [OrderFortyNineSevenHighCensus.reps] at hindex
    interval_cases index
    · exact sevenHighT2Rep0_excluded
    · exact sevenHighT2Rep1_excluded
  · simp [OrderFortyNineSevenHighCensus.reps] at hindex
    interval_cases index
    · exact sevenHighT3Rep0_excluded
    · exact sevenHighT3Rep1_excluded
    · exact sevenHighT3Rep2_excluded
  · simp [OrderFortyNineSevenHighCensus.reps] at hindex
    interval_cases index
    · exact sevenHighT4Rep0_excluded
    · exact sevenHighT4Rep1_excluded
    · exact sevenHighT4Rep2_excluded
  · simp [OrderFortyNineSevenHighCensus.reps] at hindex
    interval_cases index
    · exact sevenHighT5Rep0_excluded
    · exact sevenHighT5Rep1_excluded
  · simp [OrderFortyNineSevenHighCensus.reps] at hindex
    have hi : index = 0 := by omega
    subst index
    exact sevenHighT6Rep0_excluded
  · simp [OrderFortyNineSevenHighCensus.reps] at hindex
    have hi : index = 0 := by omega
    subst index
    exact sevenHighT7Rep0_excluded

/-- All thirteen checked canonical representatives with at least one high
triple are excluded.  The empty triple-system representative is the sole
remaining certificate input for the seven-high stratum. -/
theorem orderFortyNineStratumExcluded_seven_of_t0
    (hzero : SevenHighCanonicalRepresentativeExcluded 0 0) :
    OrderFortyNineStratumExcluded 7 :=
  orderFortyNineStratumExcluded_seven_of_t0_t1
    hzero sevenHighT1Rep0_excluded

end Erdos85
