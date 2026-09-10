import Proofs.Erdos85ThreeHighDeficientExternalFarTable
import Proofs.Erdos85ThreeHighExternalSearchCertificate

namespace Erdos85

/-- Reject a checked external obstruction before the downstream search. -/
def threeHighExternalFarPreflight {n : Nat}
    (select : (Fin 15 → Fin 15 → Bool) → Fin n → Fin 15)
    (search : ThreeHighExternalSearch) : ThreeHighExternalSearch :=
  fun U R accept => if ThreeHighExternalFarObstruction U (select U)
    then false else search U R accept

attribute [local irreducible] threeHighCrossDomain

theorem threeHighExternalFarPreflight_sound {n : Nat}
    (select : (Fin 15 → Fin 15 → Bool) → Fin n → Fin 15)
    (search : ThreeHighExternalSearch) (hs : ThreeHighExternalSearchSound search) :
    ThreeHighExternalSearchSound (threeHighExternalFarPreflight select search) := by
  intro U R accept cross hc hExt ha
  have hn : ¬ ThreeHighExternalFarObstruction U (select U) := by
    intro h
    exact h.no_external_cross U (select U) R cross hc hExt
  simp only [threeHighExternalFarPreflight,if_neg hn]
  exact hs U R accept cross hc hExt ha

theorem threeHighExternalFarPreflight_reject {n : Nat}
    (select : (Fin 15 → Fin 15 → Bool) → Fin n → Fin 15)
    (search : ThreeHighExternalSearch) (U : Fin 15 → Fin 15 → Bool)
    (R : Fin 8 → Fin 8 → Bool) (accept : ThreeHighCross → Bool)
    (h : ThreeHighExternalFarObstruction U (select U)) :
    threeHighExternalFarPreflight select search U R accept = false := by
  simp only [threeHighExternalFarPreflight,if_pos h]

theorem threeHighExternalFarPreflight_table_false
    (i : Fin 51) (search : ThreeHighExternalSearch)
    (R : Fin 8 → Fin 8 → Bool) (accept : ThreeHighCross → Bool) :
    threeHighExternalFarPreflight (fun _ => threeHighDeficientExternalFarVertices i)
      search (threeHighDeficientExternalFarAdj i) R accept = false :=
  threeHighExternalFarPreflight_reject _ search _ R accept
    (threeHighDeficientExternalFarTable_checked i)

end Erdos85
#print axioms Erdos85.threeHighExternalFarPreflight_sound
#print axioms Erdos85.threeHighExternalFarPreflight_reject
#print axioms Erdos85.threeHighExternalFarPreflight_table_false
