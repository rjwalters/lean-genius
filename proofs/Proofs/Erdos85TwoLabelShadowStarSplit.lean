import Mathlib

/-!
# Two-label shadow-star channel split

For a private unordered label pair at a port `p`, the secondary two-factor
supplies two individually labelled shadow edges `p--r₁` and `p--r₂`.  In
characteristic two the two copies of `p` in their incidence boundary cancel.
Adding the three-port footprint therefore recovers the original unit at `p`.

These are the singleton and aggregate occurrence identities
`(73rnz_cjibkzzo)--(73rnz_cjibkzzp)`.  They perform the channel change needed
by the Baer `00--00` carrier; no cancellation claim is made.
-/

namespace Erdos85

/-- The `ZMod 2` atom supported at one physical port. -/
def shadowPortAtom {P : Type*} [DecidableEq P] (p : P) : P → ZMod 2 :=
  fun v => if v = p then 1 else 0

/-- Incidence boundary of a physical shadow edge. -/
def shadowEdgeBoundary {P : Type*} [DecidableEq P] (p r : P) : P → ZMod 2 :=
  shadowPortAtom p + shadowPortAtom r

/-- Boundary of the two individually labelled shadow edges issuing from
`p`. -/
def twoLabelShadowStarBoundary {P : Type*} [DecidableEq P]
    (p r₁ r₂ : P) : P → ZMod 2 :=
  shadowEdgeBoundary p r₁ + shadowEdgeBoundary p r₂

/-- The three-port footprint retained by the channel split. -/
def twoLabelShadowFootprint {P : Type*} [DecidableEq P]
    (p r₁ r₂ : P) : P → ZMod 2 :=
  shadowPortAtom p + shadowPortAtom r₁ + shadowPortAtom r₂

/-- The star boundary contains only the two companion ports: the two copies
of its center cancel over `ZMod 2`. -/
theorem twoLabelShadowStarBoundary_eq_companionAtoms
    {P : Type*} [DecidableEq P] (p r₁ r₂ : P) :
    twoLabelShadowStarBoundary p r₁ r₂ =
      shadowPortAtom r₁ + shadowPortAtom r₂ := by
  funext v
  simp only [twoLabelShadowStarBoundary, shadowEdgeBoundary, Pi.add_apply]
  have htwo (x : ZMod 2) : x + x = 0 := by
    have hchar : (2 : ZMod 2) = 0 := by decide
    rw [← two_mul, hchar, zero_mul]
  calc
    (shadowPortAtom p v + shadowPortAtom r₁ v) +
        (shadowPortAtom p v + shadowPortAtom r₂ v) =
      (shadowPortAtom p v + shadowPortAtom p v) +
        (shadowPortAtom r₁ v + shadowPortAtom r₂ v) := by ac_rfl
    _ = 0 + (shadowPortAtom r₁ v + shadowPortAtom r₂ v) := by
      rw [htwo]
    _ = shadowPortAtom r₁ v + shadowPortAtom r₂ v := zero_add _

/-- **Singleton two-label channel split (`73rnz_cjibkzzo`).**  The private
port unit is its three-port footprint plus the incidence boundary of the two
labelled shadow edges. -/
theorem shadowPortAtom_eq_footprint_add_starBoundary
    {P : Type*} [DecidableEq P] (p r₁ r₂ : P) :
    shadowPortAtom p =
      twoLabelShadowFootprint p r₁ r₂ + twoLabelShadowStarBoundary p r₁ r₂ := by
  rw [twoLabelShadowStarBoundary_eq_companionAtoms]
  funext v
  simp only [twoLabelShadowFootprint, Pi.add_apply]
  have htwo (x : ZMod 2) : x + x = 0 := by
    have hchar : (2 : ZMod 2) = 0 := by decide
    rw [← two_mul, hchar, zero_mul]
  symm
  calc
    (shadowPortAtom p v + shadowPortAtom r₁ v + shadowPortAtom r₂ v) +
        (shadowPortAtom r₁ v + shadowPortAtom r₂ v) =
      shadowPortAtom p v +
        (shadowPortAtom r₁ v + shadowPortAtom r₁ v) +
          (shadowPortAtom r₂ v + shadowPortAtom r₂ v) := by ac_rfl
    _ = shadowPortAtom p v + 0 + 0 := by rw [htwo, htwo]
    _ = shadowPortAtom p v := by simp

/-- **Aggregate two-label channel split (`73rnz_cjibkzzp`).**  Summing over
any finite selected port census commutes with the singleton split, retaining
each physical center and its two companions. -/
theorem sum_shadowPortAtom_eq_sum_footprint_add_sum_starBoundary
    {I P : Type*} [DecidableEq I] [DecidableEq P]
    (selected : Finset I) (port companion₁ companion₂ : I → P) :
    (∑ i ∈ selected, shadowPortAtom (port i)) =
      (∑ i ∈ selected,
          twoLabelShadowFootprint (port i) (companion₁ i) (companion₂ i)) +
        ∑ i ∈ selected,
          twoLabelShadowStarBoundary (port i) (companion₁ i) (companion₂ i) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  exact shadowPortAtom_eq_footprint_add_starBoundary
    (port i) (companion₁ i) (companion₂ i)

end Erdos85

#print axioms Erdos85.twoLabelShadowStarBoundary_eq_companionAtoms
#print axioms Erdos85.shadowPortAtom_eq_footprint_add_starBoundary
#print axioms Erdos85.sum_shadowPortAtom_eq_sum_footprint_add_sum_starBoundary
