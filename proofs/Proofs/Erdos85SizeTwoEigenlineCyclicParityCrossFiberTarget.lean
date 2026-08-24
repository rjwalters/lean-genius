import Proofs.Erdos85SizeTwoEigenlineCyclicCrossOrbitPressure

/-!
# Cross-fiber target for a binary parity class

Selecting only one balanced mod-two class leaves `q/2-1` difference fibers.
For that smaller family, the earlier `q(q-4)` cross-fiber estimate is not
arithmetically strong enough.  Saving six target rows per ordered distinct
fiber pair is exactly sufficient: a uniform `q(q-6)` bound contradicts the
selected-orbit Cauchy pressure for every even `q >= 8`.

This file records a valid conditional consumer, not a proposed proof of its
hypothesis.  Exact q=8 adversarial controls show that each two-cap even pair
at `a=2` forces cross-collision mass at least `40`, while this consumer would
require at most `8*(8-6)=16`.  Thus the bound cannot follow pairwise from the
two named agreement laws; using it after assuming the inconsistent full
three-fiber package would risk a circular or vacuous argument.  The live
parity-class route must instead exploit its genuinely ternary separation
core.
-/

namespace Erdos85

noncomputable section

private theorem binary_parityClass_crossFiber_pressure_arithmetic
    (q n cross : ℕ) (hq : 8 ≤ q) (h2q : 2 ∣ q)
    (hn : n = q / 2 - 1)
    (hlower :
      n * n * (q * (q - 2)) ≤
        n * (q * (q - 2)) + n * (q * (q - 1)) + cross)
    (hupper : cross ≤ (n * n - n) * (q * (q - 6))) : False := by
  obtain ⟨k, rfl⟩ := h2q
  have hk : 4 ≤ k := by omega
  have hdiv : 2 * k / 2 = k := by omega
  rw [hdiv] at hn
  subst n
  have hnpos : 0 < k - 1 := by
    omega
  have hq7 : 0 < 2 * k - 7 := by omega
  have hpos : 0 < (k - 1) * (2 * k) * (2 * k - 7) :=
    Nat.mul_pos (Nat.mul_pos hnpos (by omega)) hq7
  have hnn : k - 1 ≤ (k - 1) * (k - 1) := by
    nlinarith
  have hpoly :
      (k - 1) * (k - 1) * (2 * k * (2 * k - 2)) =
        (k - 1) * (2 * k * (2 * k - 2)) +
          (k - 1) * (2 * k * (2 * k - 1)) +
          ((k - 1) * (k - 1) - (k - 1)) *
            (2 * k * (2 * k - 6)) +
          (k - 1) * (2 * k) * (2 * k - 7) := by
    apply Nat.cast_injective (R := ℤ)
    push_cast [Nat.cast_sub (by omega : 1 ≤ k),
      Nat.cast_sub (by omega : 2 ≤ 2 * k),
      Nat.cast_sub (by omega : 1 ≤ 2 * k),
      Nat.cast_sub (by omega : 6 ≤ 2 * k),
      Nat.cast_sub (by omega : 7 ≤ 2 * k), Nat.cast_sub hnn]
    ring
  have hle :
      (k - 1) * (k - 1) * (2 * k * (2 * k - 2)) ≤
        (k - 1) * (2 * k * (2 * k - 2)) +
          (k - 1) * (2 * k * (2 * k - 1)) +
          ((k - 1) * (k - 1) - (k - 1)) *
            (2 * k * (2 * k - 6)) :=
    hlower.trans (Nat.add_le_add_left hupper _)
  rw [hpoly] at hle
  omega

/-- On a selected family of `q/2-1` difference fibers, a uniform
`q(q-6)` bound on every ordered cross-fiber collision block is incompatible
with the exact cyclic routing laws. -/
theorem false_of_binary_sizeTwoCyclic_parityClass_crossFiberCollision_le
    (q : ℕ) [NeZero q] (hq : 8 ≤ q) (h2q : 2 ∣ q)
    (a : ZMod q) (ha : a ≠ -1 - a)
    (code : SizeTwoCyclicFullPermutationCode q a)
    (T : Finset (sizeTwoAllowedDifference q a))
    (hTcard : T.card = q / 2 - 1)
    (hcross : ∀ t ∈ T, ∀ u ∈ T, t ≠ u →
      (∑ e : SizeTwoCyclicAbsoluteGridEdge q,
        sizeTwoCyclicMatchingOrbitMultiplicity code t e *
          sizeTwoCyclicMatchingOrbitMultiplicity code u e) ≤
        q * (q - 6)) : False := by
  classical
  have hq1 : (1 : ZMod q) ≠ 0 := by
    intro h
    have := ZMod.one_eq_zero_iff.mp h
    omega
  have hpressure := sizeTwoCyclicMatchingOrbitMultiplicity_cross_pressure
    code (by omega) hq1 ha T
  let cross := ∑ p ∈ T.offDiag,
    ∑ e : SizeTwoCyclicAbsoluteGridEdge q,
      sizeTwoCyclicMatchingOrbitMultiplicity code p.1 e *
        sizeTwoCyclicMatchingOrbitMultiplicity code p.2 e
  have hcrossSum : cross ≤
      (T.card * T.card - T.card) * (q * (q - 6)) := by
    calc
      cross ≤ ∑ _p ∈ T.offDiag, q * (q - 6) := by
        apply Finset.sum_le_sum
        intro p hp
        have hm := Finset.mem_offDiag.mp hp
        exact hcross p.1 hm.1 p.2 hm.2.1 hm.2.2
      _ = (T.card * T.card - T.card) * (q * (q - 6)) := by
        simp
  exact binary_parityClass_crossFiber_pressure_arithmetic
    q T.card cross hq h2q hTcard
    (by simpa [cross] using hpressure) hcrossSum

end

end Erdos85

#print axioms
  Erdos85.false_of_binary_sizeTwoCyclic_parityClass_crossFiberCollision_le
