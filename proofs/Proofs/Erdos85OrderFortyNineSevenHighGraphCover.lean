import Proofs.Erdos85OrderFortyNineSevenHighSevenFiber

/-!
# Complete graph-side cover for the seven-high stratum

All eight possible triple-incidence counts are now normalized to the fourteen
canonical Boolean representatives.  Certificate exclusion is the only input
remaining at this interface.
-/

namespace Erdos85

theorem sevenHighCanonicalGraphCover_all
    (blocks : Nat) (hblocks : blocks ≤ 7) :
    SevenHighCanonicalGraphCover blocks := by
  interval_cases blocks
  · exact sevenHighCanonicalGraphCover_zero
  · exact sevenHighCanonicalGraphCover_one
  · exact sevenHighCanonicalGraphCover_two
  · exact sevenHighCanonicalGraphCover_three
  · exact sevenHighCanonicalGraphCover_four
  · exact sevenHighCanonicalGraphCover_five
  · exact sevenHighCanonicalGraphCover_six
  · exact sevenHighCanonicalGraphCover_seven

theorem orderFortyNineStratumExcluded_seven_of_certificates
    (hexcluded : ∀ blocks index, blocks ≤ 7 →
      index < (OrderFortyNineSevenHighCensus.reps blocks).length →
        SevenHighCanonicalRepresentativeExcluded blocks index) :
    OrderFortyNineStratumExcluded 7 :=
  orderFortyNineStratumExcluded_seven_of_canonical
    sevenHighCanonicalGraphCover_all hexcluded

end Erdos85
