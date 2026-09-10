import U20Coordinates
import U20DomainReasons
namespace U20CoverageInputs
open Erdos85 U20CoverageLiterals
attribute [local irreducible] threeHighCrossDomain

theorem swaps_valid : threeHighRSwapPairsValid R [(2,3),(4,5),(6,7)] = true := by decide

theorem domains_complete (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (he : encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow = true) :
    ∀ j, threeHighCrossColumns cross j ∈ domains j :=
  threeHighWitnessedColumnDomainsCheck_complete U R domains U20CoverageDomains.reasons
    U20CoverageDomains.checked cross hc he

end U20CoverageInputs
#print axioms U20CoverageInputs.swaps_valid
#print axioms U20CoverageInputs.domains_complete
