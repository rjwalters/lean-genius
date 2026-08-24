import Proofs.Erdos85CrossNeighborhoodFlipDefectExpansion

/-!
# T-word gauge parity on a paired witness star

This file formalizes `(73rnz_cjiba)`.  Each paired relay has two endpoint
T-bits.  The mixed-word census is exactly the total endpoint incidence, and
the sum of the `00` and `11` censuses is the pair-count plus that incidence.
Thus even T-degree removes mixed words, while an even number of pairs leaves
one common `00/11` gauge bit.
-/

namespace Erdos85

/-- Indicator of a mixed `01` or `10` relay word. -/
def pairedStarMixedWord (left right : ZMod 2) : ZMod 2 :=
  left * (1 + right) + (1 + left) * right

/-- Indicator of a `00` relay word. -/
def pairedStarWord00 (left right : ZMod 2) : ZMod 2 :=
  (1 + left) * (1 + right)

/-- Indicator of a `11` relay word. -/
def pairedStarWord11 (left right : ZMod 2) : ZMod 2 := left * right

/-- Pointwise, mixed-word activity is the sum of the two endpoint T-bits. -/
theorem pairedStarMixedWord_eq_endpoint_sum (left right : ZMod 2) :
    pairedStarMixedWord left right = left + right := by
  unfold pairedStarMixedWord
  have htwo : (2 : ZMod 2) = 0 := by decide
  ring_nf
  simp [htwo]

/-- Pointwise polarization: `00 + 11 = 1 + left + right`. -/
theorem pairedStarWord00_add_word11_eq
    (left right : ZMod 2) :
    pairedStarWord00 left right + pairedStarWord11 left right =
      1 + left + right := by
  unfold pairedStarWord00 pairedStarWord11
  have htwo : (2 : ZMod 2) = 0 := by decide
  ring_nf
  simp [htwo]

/-- The mixed relay census equals total marked endpoint incidence, independent
of the chosen star pairing. -/
theorem pairedStar_mixedWord_sum_eq_endpointMass
    {Pair : Type*} [Fintype Pair]
    (left right : Pair → ZMod 2) :
    (∑ p, pairedStarMixedWord (left p) (right p)) =
      (∑ p, left p) + ∑ p, right p := by
  simp_rw [pairedStarMixedWord_eq_endpoint_sum, Finset.sum_add_distrib]

/-- The combined same-word census is pair-count plus endpoint mass. -/
theorem pairedStar_word00_add_word11_sum_eq
    {Pair : Type*} [Fintype Pair]
    (left right : Pair → ZMod 2) :
    (∑ p, pairedStarWord00 (left p) (right p)) +
        (∑ p, pairedStarWord11 (left p) (right p)) =
      (Fintype.card Pair : ZMod 2) +
        (∑ p, left p) + ∑ p, right p := by
  rw [← Finset.sum_add_distrib]
  simp_rw [pairedStarWord00_add_word11_eq]
  rw [show (∑ p : Pair, ((1 : ZMod 2) + left p + right p)) =
      ((∑ _p : Pair, (1 : ZMod 2)) +
        (∑ p : Pair, left p) + (∑ p : Pair, right p)) by
          simp_rw [Finset.sum_add_distrib]]
  simp

/-- Even T-degree forces the mixed `01/10` relay population to be even. -/
theorem pairedStar_mixedWord_sum_eq_zero_of_endpointMass_zero
    {Pair : Type*} [Fintype Pair]
    (left right : Pair → ZMod 2)
    (hmarked : (∑ p, left p) + ∑ p, right p = 0) :
    (∑ p, pairedStarMixedWord (left p) (right p)) = 0 := by
  rw [pairedStar_mixedWord_sum_eq_endpointMass, hmarked]

/-- If the number of pairs is even (in the audit, `q/2 = 0 mod 2`) and the
T-degree is even, the `00` and `11` cells carry exactly the same gauge bit. -/
theorem pairedStar_word00_sum_eq_word11_sum
    {Pair : Type*} [Fintype Pair]
    (left right : Pair → ZMod 2)
    (hpairs : (Fintype.card Pair : ZMod 2) = 0)
    (hmarked : (∑ p, left p) + ∑ p, right p = 0) :
    (∑ p, pairedStarWord00 (left p) (right p)) =
      ∑ p, pairedStarWord11 (left p) (right p) := by
  have hsum := pairedStar_word00_add_word11_sum_eq left right
  rw [hpairs] at hsum
  simp only [zero_add] at hsum
  rw [hmarked] at hsum
  have htwo : (2 : ZMod 2) = 0 := by decide
  let a := ∑ p, pairedStarWord00 (left p) (right p)
  let b := ∑ p, pairedStarWord11 (left p) (right p)
  change a + b = 0 at hsum
  change a = b
  calc
    a = a + 0 := by simp
    _ = a + (a + b) := by rw [hsum]
    _ = (a + a) + b := by ring
    _ = b := by rw [← two_mul, htwo, zero_mul, zero_add]

end Erdos85

#print axioms Erdos85.pairedStar_mixedWord_sum_eq_endpointMass
#print axioms Erdos85.pairedStar_word00_add_word11_sum_eq
#print axioms Erdos85.pairedStar_mixedWord_sum_eq_zero_of_endpointMass_zero
#print axioms Erdos85.pairedStar_word00_sum_eq_word11_sum
