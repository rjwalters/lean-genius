import Proofs.Erdos85SizeTwoEigenlineCyclicQuotient

/-!
# Even-order reflection arithmetic

Node: `BinarySizeTwoCyclicPackingBound` beneath outline F.3.

At even cyclic order, the two forbidden shifts `a` and `-1-a` are
automatically distinct: equality would reduce modulo two to `0 = 1`.
Consequently all allowed-difference and exterior-cell cardinality formulas
used by the binary packing route require no separate distinctness hypothesis.
-/

namespace Erdos85

noncomputable section

/-- The two shifts in a reflection pair are distinct at every nonzero even
modulus. -/
theorem sizeTwoReflection_shifts_ne_of_even
    {q : ℕ} [NeZero q] (hqEven : Even q) (a : ZMod q) :
    a ≠ -1 - a := by
  have hq2 : 2 ∣ q := even_iff_two_dvd.mp hqEven
  intro h
  let φ : ZMod q →+* ZMod 2 := ZMod.castHom hq2 (ZMod 2)
  have hz := congrArg φ h
  have htwo : φ a + φ a = -1 := by
    calc
      φ a + φ a = φ (-1 - a) + φ a := by rw [hz]
      _ = -1 := by rw [map_sub, map_neg, map_one]; ring
  have hzero : φ a + φ a = 0 := by
    calc
      φ a + φ a = 2 * φ a := by ring
      _ = 0 := by rw [show (2 : ZMod 2) = 0 by decide]; simp
  rw [hzero] at htwo
  norm_num at htwo

/-- At even order there are exactly `q-2` allowed difference fibers. -/
theorem sizeTwoAllowedDifference_card_of_even
    (q : ℕ) [NeZero q] (hqEven : Even q) (a : ZMod q) :
    Fintype.card (sizeTwoAllowedDifference q a) = q - 2 :=
  sizeTwoAllowedDifference_card q a
    (sizeTwoReflection_shifts_ne_of_even hqEven a)

/-- At even order the cyclic exterior grid has exactly `q(q-2)` cells. -/
theorem sizeTwoCyclicExteriorCell_card_of_even
    (q : ℕ) [NeZero q] (hqEven : Even q) (a : ZMod q) :
    Fintype.card (sizeTwoCyclicExteriorCell q a) = q * (q - 2) :=
  sizeTwoCyclicExteriorCell_card q a
    (sizeTwoReflection_shifts_ne_of_even hqEven a)

end


end Erdos85

#print axioms Erdos85.sizeTwoReflection_shifts_ne_of_even
#print axioms Erdos85.sizeTwoAllowedDifference_card_of_even
#print axioms Erdos85.sizeTwoCyclicExteriorCell_card_of_even
