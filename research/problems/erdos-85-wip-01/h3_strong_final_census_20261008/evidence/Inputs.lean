import CoverageCoordinates
import DomainReasons
namespace ColumnCoverageInputs
open Erdos85 ColumnCoverageLiterals
attribute [local irreducible] threeHighCrossDomain

theorem swaps_valid : threeHighRSwapPairsValid R [(2,3),(4,5),(6,7)] = true := by decide

theorem domains_complete (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (he : encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow = true) :
    ∀ j, threeHighCrossColumns cross j ∈ domains j :=
  threeHighWitnessedColumnDomainsCheck_complete U R domains ColumnCoverageDomains.reasons
    ColumnCoverageDomains.checked cross hc he

end ColumnCoverageInputs
#print axioms ColumnCoverageInputs.swaps_valid
#print axioms ColumnCoverageInputs.domains_complete
