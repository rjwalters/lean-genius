import Proofs.Erdos85ThreeHighFarColorCertificate
import Proofs.Erdos85ThreeHighExternalSearchCertificate

namespace Erdos85

/-- A selected-label certificate may reject only when both far-edge directions hold. -/
def threeHighFarColorPreflight {n : Nat}
    (select : (Fin 15 → Fin 15 → Bool) → Fin n → Fin 15)
    (search : ThreeHighExternalSearch) : ThreeHighExternalSearch :=
  fun U R accept =>
    if R 6 7 = true ∧ R 7 6 = true ∧ ThreeHighFarColorObstruction U (select U)
    then false else search U R accept

attribute [local irreducible] threeHighCrossDomain

theorem threeHighFarColorPreflight_sound {n : Nat}
    (select : (Fin 15 → Fin 15 → Bool) → Fin n → Fin 15)
    (search : ThreeHighExternalSearch) (hs : ThreeHighExternalSearchSound search) :
    ThreeHighExternalSearchSound (threeHighFarColorPreflight select search) := by
  intro U R accept cross hc hExt ha
  have hn : ¬ (R 6 7 = true ∧ R 7 6 = true ∧ ThreeHighFarColorObstruction U (select U)) := by
    rintro ⟨h67,h76,h⟩
    exact h.no_cross U (select U) R h67 h76 cross hc
  simp only [threeHighFarColorPreflight,if_neg hn]
  exact hs U R accept cross hc hExt ha

theorem threeHighFarColorPreflight_reject {n : Nat}
    (select : (Fin 15 → Fin 15 → Bool) → Fin n → Fin 15)
    (search : ThreeHighExternalSearch) (U : Fin 15 → Fin 15 → Bool)
    (R : Fin 8 → Fin 8 → Bool) (accept : ThreeHighCross → Bool)
    (h67 : R 6 7 = true) (h76 : R 7 6 = true)
    (h : ThreeHighFarColorObstruction U (select U)) :
    threeHighFarColorPreflight select search U R accept = false := by
  have hcond : R 6 7 = true ∧ R 7 6 = true ∧ ThreeHighFarColorObstruction U (select U) :=
    ⟨h67,h76,h⟩
  simp only [threeHighFarColorPreflight,if_pos hcond]

end Erdos85
#print axioms Erdos85.threeHighFarColorPreflight_sound
#print axioms Erdos85.threeHighFarColorPreflight_reject
