import Proofs.Erdos85ThreeHighFarColorPreflight
import Proofs.Erdos85ThreeHighFullFarColorTable
import Proofs.Erdos85ThreeHighDeficientFarColorTable

namespace Erdos85

/-- Each full-table certificate rejects any downstream search when the far edge exists. -/
theorem threeHighFullFarColorTable_search_false (i : Fin 14)
    (search : ThreeHighExternalSearch) (R : Fin 8 → Fin 8 → Bool)
    (accept : ThreeHighCross → Bool) (h67 : R 6 7 = true) (h76 : R 7 6 = true) :
    threeHighFarColorPreflight (fun _ => threeHighFullFarColorVertices i)
      search (threeHighFullFarColorTableAdj i) R accept = false := by
  exact threeHighFarColorPreflight_reject _ search _ R accept h67 h76
    (threeHighFullFarColorTable_checked i)

/-- Each deficient-table certificate retains the same explicit far-edge requirement. -/
theorem threeHighDeficientFarColorTable_search_false (i : Fin 89)
    (search : ThreeHighExternalSearch) (R : Fin 8 → Fin 8 → Bool)
    (accept : ThreeHighCross → Bool) (h67 : R 6 7 = true) (h76 : R 7 6 = true) :
    threeHighFarColorPreflight (fun _ => threeHighDeficientFarColorVertices i)
      search (threeHighDeficientFarColorTableAdj i) R accept = false := by
  exact threeHighFarColorPreflight_reject _ search _ R accept h67 h76
    (threeHighDeficientFarColorTable_checked i)

end Erdos85
#print axioms Erdos85.threeHighFullFarColorTable_search_false
#print axioms Erdos85.threeHighDeficientFarColorTable_search_false
