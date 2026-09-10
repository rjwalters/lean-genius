import Proofs.Erdos85ThreeHighLowDegreePair
import Proofs.Erdos85ThreeHighExternalSearchCertificate

namespace Erdos85

/-- Only low-degree rows need be compared for the far-label pair obstruction. -/
def threeHighLowDegreePairGate (U : Fin 15 → Fin 15 → Bool) : Bool :=
  let large := (List.finRange 15).filter (fun x => decide (encodedRowDegree (U x) ≤ 1))
  let low := (List.finRange 15).filter (fun y => decide (encodedRowDegree (U y) ≤ 2))
  large.all fun x => low.all fun y => decide (x = y ∨ ¬ ∃ s, U x s = true ∧ U y s = true)

attribute [local irreducible] threeHighCrossDomain

theorem threeHighLowDegreePairGate_of_cross
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R) :
    threeHighLowDegreePairGate U = true := by
  apply List.all_eq_true.mpr
  intro x hx
  apply List.all_eq_true.mpr
  intro y hy
  apply decide_eq_true_iff.mpr
  by_cases hxy : x = y
  · exact Or.inl hxy
  · apply Or.inr
    rintro ⟨s,hxs,hys⟩
    exact threeHighCrossDomain_no_low_degree_pair U R cross hc x y s hxy
      (of_decide_eq_true (List.mem_filter.mp hx).2)
      (of_decide_eq_true (List.mem_filter.mp hy).2) hxs hys

def threeHighPairPreflight (search : ThreeHighExternalSearch) : ThreeHighExternalSearch :=
  fun U R accept => threeHighLowDegreePairGate U && search U R accept

theorem threeHighPairPreflight_sound (search : ThreeHighExternalSearch)
    (hs : ThreeHighExternalSearchSound search) :
    ThreeHighExternalSearchSound (threeHighPairPreflight search) := by
  intro U R accept cross hc hExt ha
  simp only [threeHighPairPreflight,Bool.and_eq_true]
  exact ⟨threeHighLowDegreePairGate_of_cross U R cross hc,hs U R accept cross hc hExt ha⟩

end Erdos85
#print axioms Erdos85.threeHighLowDegreePairGate_of_cross
#print axioms Erdos85.threeHighPairPreflight_sound
