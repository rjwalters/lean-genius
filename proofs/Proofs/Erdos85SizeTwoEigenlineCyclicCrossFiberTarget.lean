import Proofs.Erdos85SizeTwoEigenlineCyclicCrossOrbitPressure
import Proofs.Erdos85SizeTwoEigenlineCyclicEvenReflection

/-!
# The cross-fiber estimate sufficient for binary cyclic packing

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

The aggregate countermodel shows that moments alone leave the ordered
cross-fiber term unconstrained.  This file isolates a concrete replacement:
saving two target rows per base, i.e. bounding every distinct ordered fiber
pair by `q(q-4)`, contradicts the sharp-support Cauchy pressure when all
`q-2` fibers are selected.  The remaining mathematical gap is now exactly
this displacement-resolved cross-fiber bound.
-/

namespace Erdos85

noncomputable section

private theorem binary_crossFiber_pressure_arithmetic
    (q cross : ℕ) (hq : 8 ≤ q)
    (hlower :
      (q - 2) * (q - 2) * (q * (q - 2)) ≤
        (q - 2) * (q * (q - 2)) +
          (q - 2) * (q * (q - 1)) + cross)
    (hupper : cross ≤
      ((q - 2) * (q - 2) - (q - 2)) * (q * (q - 4))) : False := by
  have hpos : 0 < q * (q - 5) * (q - 2) :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hsq : q - 2 ≤ (q - 2) * (q - 2) := by nlinarith
  have hpoly :
      (q - 2) * (q - 2) * (q * (q - 2)) =
        (q - 2) * (q * (q - 2)) +
          (q - 2) * (q * (q - 1)) +
          ((q - 2) * (q - 2) - (q - 2)) * (q * (q - 4)) +
          q * (q - 5) * (q - 2) := by
    apply Nat.cast_injective (R := ℤ)
    push_cast [Nat.cast_sub (by omega : 2 ≤ q),
      Nat.cast_sub (by omega : 1 ≤ q),
      Nat.cast_sub (by omega : 4 ≤ q),
      Nat.cast_sub (by omega : 5 ≤ q), Nat.cast_sub hsq]
    ring
  have hle :
      (q - 2) * (q - 2) * (q * (q - 2)) ≤
        (q - 2) * (q * (q - 2)) +
          (q - 2) * (q * (q - 1)) +
          ((q - 2) * (q - 2) - (q - 2)) * (q * (q - 4)) :=
    hlower.trans (Nat.add_le_add_left hupper _)
  rw [hpoly] at hle
  omega

/-- A uniform `q(q-4)` upper bound on the ordered collision mass of every
two distinct difference fibers rules out a full reciprocal cyclic code at
every even `q ≥ 8`. -/
theorem false_of_binary_sizeTwoCyclic_crossFiberCollision_le
    (q : ℕ) [NeZero q] (hq : 8 ≤ q) (hqEven : Even q)
    (a : ZMod q)
    (code : SizeTwoCyclicFullPermutationCode q a)
    (hcross : ∀ t u : sizeTwoAllowedDifference q a, t ≠ u →
      (∑ e : SizeTwoCyclicAbsoluteGridEdge q,
        sizeTwoCyclicMatchingOrbitMultiplicity code t e *
          sizeTwoCyclicMatchingOrbitMultiplicity code u e) ≤
        q * (q - 4)) : False := by
  classical
  have hq1 : (1 : ZMod q) ≠ 0 := by
    intro h
    have := ZMod.one_eq_zero_iff.mp h
    omega
  have ha : a ≠ -1 - a := sizeTwoReflection_shifts_ne_of_even hqEven a
  have hpressure := sizeTwoCyclicMatchingOrbitMultiplicity_cross_pressure
    code (by omega) hq1 ha Finset.univ
  have hcard : Fintype.card (sizeTwoAllowedDifference q a) = q - 2 :=
    sizeTwoAllowedDifference_card_of_even q hqEven a
  simp only [Finset.card_univ, hcard] at hpressure
  let cross := ∑ p ∈
      (Finset.univ : Finset (sizeTwoAllowedDifference q a)).offDiag,
        ∑ e : SizeTwoCyclicAbsoluteGridEdge q,
          sizeTwoCyclicMatchingOrbitMultiplicity code p.1 e *
            sizeTwoCyclicMatchingOrbitMultiplicity code p.2 e
  have hcrossSum : cross ≤
      ((q - 2) * (q - 2) - (q - 2)) * (q * (q - 4)) := by
    calc
      cross ≤ ∑ _p ∈
          (Finset.univ : Finset
            (sizeTwoAllowedDifference q a)).offDiag,
          q * (q - 4) := by
        apply Finset.sum_le_sum
        intro p hp
        exact hcross p.1 p.2 (Finset.mem_offDiag.mp hp).2.2
      _ = ((q - 2) * (q - 2) - (q - 2)) * (q * (q - 4)) := by
        simp [hcard]
  exact binary_crossFiber_pressure_arithmetic q cross hq
    (by simpa [cross] using hpressure) hcrossSum

end

end Erdos85

#print axioms
  Erdos85.false_of_binary_sizeTwoCyclic_crossFiberCollision_le
