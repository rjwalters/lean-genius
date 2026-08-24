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

/-- Reflection in `-1/2` preserves the allowed difference fibres. -/
def sizeTwoAllowedDifferenceReflection
    (q : ℕ) [NeZero q] (a : ZMod q) :
    sizeTwoAllowedDifference q a ≃ sizeTwoAllowedDifference q a where
  toFun t := ⟨-1 - t.1, by
    constructor
    · intro h
      apply t.2.2
      calc
        t.1 = -1 - (-1 - t.1) := by abel
        _ = -1 - a := by rw [h]
    · intro h
      apply t.2.1
      calc
        t.1 = -1 - (-1 - t.1) := by abel
        _ = -1 - (-1 - a) := by rw [h]
        _ = a := by abel⟩
  invFun t := ⟨-1 - t.1, by
    constructor
    · intro h
      apply t.2.2
      calc
        t.1 = -1 - (-1 - t.1) := by abel
        _ = -1 - a := by rw [h]
    · intro h
      apply t.2.1
      calc
        t.1 = -1 - (-1 - t.1) := by abel
        _ = -1 - (-1 - a) := by rw [h]
        _ = a := by abel⟩
  left_inv t := by apply Subtype.ext; dsimp; abel
  right_inv t := by apply Subtype.ext; dsimp; abel

@[simp] theorem sizeTwoAllowedDifferenceReflection_val
    {q : ℕ} [NeZero q] {a : ZMod q}
    (t : sizeTwoAllowedDifference q a) :
    (sizeTwoAllowedDifferenceReflection q a t).1 = -1 - t.1 := rfl

/-- At even order the allowed-fibre reflection has no fixed point, so its
orbits are genuine pairs. -/
theorem sizeTwoAllowedDifferenceReflection_ne_of_even
    {q : ℕ} [NeZero q] (hqEven : Even q) {a : ZMod q}
    (t : sizeTwoAllowedDifference q a) :
    sizeTwoAllowedDifferenceReflection q a t ≠ t := by
  intro h
  have hval := congrArg Subtype.val h
  exact sizeTwoReflection_shifts_ne_of_even hqEven t.1 hval.symm

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
#print axioms Erdos85.sizeTwoAllowedDifferenceReflection_ne_of_even
#print axioms Erdos85.sizeTwoAllowedDifference_card_of_even
#print axioms Erdos85.sizeTwoCyclicExteriorCell_card_of_even
