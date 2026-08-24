import Proofs.Erdos85CrossNeighborhoodFlipDefectExpansion

/-!
# Third-color export of a simultaneously closed `00` curl

This is the finite `F₂` algebra in `(73rnz_cjibkzzz)--(73rnz_cjibkzzzd)`.
The simultaneous routing identity is exposed as `hSRP`; closing both endpoint
shores kills its endpoint terms, while odd shore orders make its rank-one
term equal to one.  If the secondary color term is also zero, a genuinely
new color must carry odd overlap.
-/

namespace Erdos85

private theorem zmod2_eq_zero_or_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  fin_cases z
  · left
    rfl
  · right
    rfl

/-- Colors other than the two endpoint colors of an SRP identity. -/
def srpThirdColors {Color : Type*} [Fintype Color] [DecidableEq Color]
    (c e : Color) : Finset Color := (Finset.univ.erase c).erase e

/-- Closed endpoint terms and odd shore masses reduce the simultaneous
routing identity to the all-horizontal third-color sum `(73rnz_cjibkzzza)`.
-/
theorem closedCurl_thirdColorOverlap_sum_eq_one
    {Color : Type*} [Fintype Color] [DecidableEq Color]
    (c e : Color) (endpointC endpointE shoreC shoreE : ZMod 2)
    (overlap : Color → ZMod 2)
    (hSRP : endpointC + endpointE +
        (∑ a ∈ srpThirdColors c e, overlap a) = shoreC * shoreE)
    (hclosedC : endpointC = 0) (hclosedE : endpointE = 0)
    (hoddC : shoreC = 1) (hoddE : shoreE = 1) :
    (∑ a ∈ srpThirdColors c e, overlap a) = 1 := by
  rw [hclosedC, hclosedE, hoddC, hoddE] at hSRP
  simpa using hSRP

/-- If one excluded secondary color has zero overlap, an odd third-color
sum is carried by a genuinely new color `(73rnz_cjibkzzzb)--(kzzzd)`. -/
theorem exists_newColor_overlap_one_of_sum_eq_one_of_secondary_zero
    {Color : Type*} [Fintype Color] [DecidableEq Color]
    (c e d : Color) (overlap : Color → ZMod 2)
    (hsum : (∑ a ∈ srpThirdColors c e, overlap a) = 1)
    (hdzero : overlap d = 0) :
    ∃ a, a ≠ c ∧ a ≠ e ∧ a ≠ d ∧ overlap a = 1 := by
  by_contra hno
  push Not at hno
  have hallZero : ∀ a ∈ srpThirdColors c e, overlap a = 0 := by
    intro a ha
    have haec : a ≠ e ∧ a ≠ c := by
      simpa [srpThirdColors] using ha
    have hac : a ≠ c := haec.2
    have hae : a ≠ e := haec.1
    by_cases had : a = d
    · simpa [had] using hdzero
    · have hnotOne : overlap a ≠ 1 := by
        exact fun hone => hno a hac hae had hone
      have hbinary := zmod2_eq_zero_or_one (overlap a)
      exact hbinary.resolve_right hnotOne
  rw [Finset.sum_eq_zero (fun a ha => hallZero a (by simpa using ha))] at hsum
  exact zero_ne_one hsum

/-- Capstone form: a closed odd curl whose secondary-color component is
complete exports to a new color with odd overlap. -/
theorem closedCurl_exists_newColor_overlap_one
    {Color : Type*} [Fintype Color] [DecidableEq Color]
    (c e d : Color) (endpointC endpointE shoreC shoreE : ZMod 2)
    (overlap : Color → ZMod 2)
    (hSRP : endpointC + endpointE +
        (∑ a ∈ srpThirdColors c e, overlap a) = shoreC * shoreE)
    (hclosedC : endpointC = 0) (hclosedE : endpointE = 0)
    (hoddC : shoreC = 1) (hoddE : shoreE = 1)
    (hdzero : overlap d = 0) :
    ∃ a, a ≠ c ∧ a ≠ e ∧ a ≠ d ∧ overlap a = 1 := by
  apply exists_newColor_overlap_one_of_sum_eq_one_of_secondary_zero
    c e d overlap
  · exact closedCurl_thirdColorOverlap_sum_eq_one c e
      endpointC endpointE shoreC shoreE overlap hSRP
      hclosedC hclosedE hoddC hoddE
  · exact hdzero

end Erdos85

#print axioms Erdos85.closedCurl_thirdColorOverlap_sum_eq_one
#print axioms Erdos85.exists_newColor_overlap_one_of_sum_eq_one_of_secondary_zero
#print axioms Erdos85.closedCurl_exists_newColor_overlap_one
