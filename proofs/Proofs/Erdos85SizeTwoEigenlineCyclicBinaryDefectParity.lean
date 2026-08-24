import Proofs.Erdos85SizeTwoEigenlineCyclicDefectCirculation

/-!
# Binary parity of sharp cyclic defects

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

For `4 ∣ q`, the forced displacement of a collision-one row has odd
projection to `ZMod 2`.  Hence its duplicated and missing target fibers have
opposite parity.  Together with defect circulation, the sharp subsystem is a
bipartite directed circulation on the allowed difference fibers.
-/

namespace Erdos85

noncomputable section

private theorem triangular_even_of_four_dvd
    (q : ℕ) (h4q : 4 ∣ q) : Even (q * (q - 1) / 2) := by
  obtain ⟨k, rfl⟩ := h4q
  refine ⟨k * (4 * k - 1), ?_⟩
  calc
    4 * k * (4 * k - 1) / 2 =
        (2 * (2 * k * (4 * k - 1))) / 2 := by congr 1; ring
    _ = 2 * k * (4 * k - 1) :=
      Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)
    _ = k * (4 * k - 1) + k * (4 * k - 1) := by ring

/-- Every base/target-fibre pair belongs to a unique adjacent base pair whose
left endpoint has the target fibre's mod-two parity.  This is the exact
partition behind the parity-selected missing-rank sum. -/
theorem existsUnique_paritySelectedAdjacentBase
    {q : ℕ} [NeZero q] (h2q : 2 ∣ q) (b u : ZMod q) :
    ∃! x : ZMod q,
      (b = x ∨ b = x + 1) ∧
        ZMod.castHom h2q (ZMod 2) u =
          ZMod.castHom h2q (ZMod 2) x := by
  let φ : ZMod q →+* ZMod 2 := ZMod.castHom h2q (ZMod 2)
  by_cases hsame : φ u = φ b
  · refine ⟨b, ⟨Or.inl rfl, hsame⟩, ?_⟩
    intro x hx
    rcases hx.1 with rfl | hshift
    · rfl
    · have hmap := congrArg φ hshift
      rw [map_add, map_one] at hmap
      have hpar : φ b = φ x := hsame.symm.trans hx.2
      have hzeroOne : (0 : ZMod 2) = 1 := by
        linear_combination hmap - hpar
      exact (zero_ne_one hzeroOne).elim
  · have hpar : φ u = φ (b - 1) := by
      rw [map_sub, map_one]
      exact (show ∀ x y : ZMod 2, x ≠ y → x = y - 1 by decide) _ _ hsame
    refine ⟨b - 1, ⟨Or.inr (by abel), hpar⟩, ?_⟩
    intro x hx
    rcases hx.1 with hbase | hshift
    · have hux : φ u = φ b := by rw [hbase]; exact hx.2
      exact (hsame hux).elim
    · rw [hshift]
      ring

/-- Canonical color of a base/target-fibre slot in the PMR partition: the
unique adjacent-window left endpoint whose parity agrees with the target
fibre. -/
noncomputable def sizeTwoCyclicParitySlotColor
    {q : ℕ} [NeZero q] (h2q : 2 ∣ q) (b u : ZMod q) : ZMod q :=
  Classical.choose (existsUnique_paritySelectedAdjacentBase h2q b u)

/-- The canonical slot color selects an adjacent window and has the target
fibre's mod-two parity. -/
theorem sizeTwoCyclicParitySlotColor_spec
    {q : ℕ} [NeZero q] (h2q : 2 ∣ q) (b u : ZMod q) :
    (b = sizeTwoCyclicParitySlotColor h2q b u ∨
      b = sizeTwoCyclicParitySlotColor h2q b u + 1) ∧
    ZMod.castHom h2q (ZMod 2) u =
      ZMod.castHom h2q (ZMod 2)
        (sizeTwoCyclicParitySlotColor h2q b u) :=
  (Classical.choose_spec
    (existsUnique_paritySelectedAdjacentBase h2q b u)).1

/-- Any adjacent-window endpoint satisfying the parity rule is the
canonical slot color. -/
theorem sizeTwoCyclicParitySlotColor_eq_of_spec
    {q : ℕ} [NeZero q] (h2q : 2 ∣ q) (b u x : ZMod q)
    (hx : (b = x ∨ b = x + 1) ∧
      ZMod.castHom h2q (ZMod 2) u =
        ZMod.castHom h2q (ZMod 2) x) :
    sizeTwoCyclicParitySlotColor h2q b u = x := by
  exact (existsUnique_paritySelectedAdjacentBase h2q b u).unique
    (sizeTwoCyclicParitySlotColor_spec h2q b u) hx

/-- The duplicate and missing fibers of a sharp row have different mod-two
projections whenever `4 ∣ q`. -/
theorem sizeTwoCyclic_singleDuplicateMissing_parity_ne
    {q : ℕ} [NeZero q] (h4q : 4 ∣ q)
    {duplicate missing t : ZMod q}
    (hdisp : duplicate - missing =
      2 * (t + 1) - (((q * (q - 1) / 2 : ℕ) : ZMod q) + 1)) :
    ZMod.castHom (dvd_trans (by norm_num : 2 ∣ 4) h4q) (ZMod 2) duplicate ≠
      ZMod.castHom (dvd_trans (by norm_num : 2 ∣ 4) h4q) (ZMod 2) missing := by
  let h2q : 2 ∣ q := dvd_trans (by norm_num : 2 ∣ 4) h4q
  let φ : ZMod q →+* ZMod 2 := ZMod.castHom h2q (ZMod 2)
  have heven := triangular_even_of_four_dvd q h4q
  have htri : φ (((q * (q - 1) / 2 : ℕ) : ZMod q)) = 0 := by
    obtain ⟨k, hk⟩ := heven
    rw [hk, Nat.cast_add, map_add]
    have htwo : (2 : ZMod 2) = 0 := by decide
    calc
      φ (k : ZMod q) + φ (k : ZMod q) = 2 * φ (k : ZMod q) := (two_mul _).symm
      _ = 0 := by rw [htwo, zero_mul]
  have htwoMap : φ (2 : ZMod q) = 0 := by
    simpa only [map_ofNat] using (show (2 : ZMod 2) = 0 by decide)
  intro heq
  have h := congrArg φ hdisp
  rw [map_sub, heq, sub_self, map_sub, map_mul, htwoMap, zero_mul,
    map_add, htri, map_one, zero_add] at h
  have hnegOne : -(1 : ZMod 2) = 1 := by decide
  rw [zero_sub, hnegOne] at h
  exact zero_ne_one h

/-- For every source row, not only a sharp one, the deviation of its
target-difference multiplicity word from the all-ones profile has nonzero
order-two Fourier moment.  This is the local parity input for PMR. -/
theorem sizeTwoCyclicTargetDifferenceMultiplicity_deviation_parity_eq_one
    {q : ℕ} [NeZero q] (h4q : 4 ∣ q) {a : ZMod q}
    (ha : a ≠ -1 - a)
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) :
    let φ : ZMod q →+* ZMod 2 :=
      ZMod.castHom (dvd_trans (by norm_num : 2 ∣ 4) h4q) (ZMod 2)
    φ ((∑ u : sizeTwoAllowedDifference q a,
        (sizeTwoCyclicTargetDifferenceMultiplicity code x t u : ZMod q) *
          u.1) -
      (∑ u : sizeTwoAllowedDifference q a, u.1)) = 1 := by
  let h2q : 2 ∣ q := dvd_trans (by norm_num : 2 ∣ 4) h4q
  let φ : ZMod q →+* ZMod 2 := ZMod.castHom h2q (ZMod 2)
  change φ ((∑ u : sizeTwoAllowedDifference q a,
      (sizeTwoCyclicTargetDifferenceMultiplicity code x t u : ZMod q) *
        u.1) -
    (∑ u : sizeTwoAllowedDifference q a, u.1)) = 1
  have hq : 2 ≤ q := by
    obtain ⟨k, hk⟩ := h4q
    have hk0 : k ≠ 0 := by
      intro hkzero
      subst k
      simp at hk
      exact NeZero.ne q hk
    omega
  rw [sizeTwoCyclicTargetDifferenceMultiplicity_deviation_sum
    hq ha code x t]
  have heven := triangular_even_of_four_dvd q h4q
  have htri : φ (((q * (q - 1) / 2 : ℕ) : ZMod q)) = 0 := by
    obtain ⟨k, hk⟩ := heven
    rw [hk, Nat.cast_add, map_add]
    have htwo : (2 : ZMod 2) = 0 := by decide
    calc
      φ (k : ZMod q) + φ (k : ZMod q) =
          2 * φ (k : ZMod q) := (two_mul _).symm
      _ = 0 := by rw [htwo, zero_mul]
  have htwoMap : φ (2 : ZMod q) = 0 := by
    simpa only [map_ofNat] using (show (2 : ZMod 2) = 0 by decide)
  rw [map_sub, map_mul, htwoMap, zero_mul, map_add, htri,
    map_one, zero_add, zero_sub]
  decide

/-- Direct cyclic-code form: collision mass one produces a duplicate/missing
pair crossing the parity partition. -/
theorem exists_paritySeparated_duplicateMissing_of_collision_eq_one
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) (h4q : 4 ∣ q) {a : ZMod q}
    [DecidableEq (sizeTwoAllowedDifference q a)]
    (ha : a ≠ -1 - a) (hq1 : (1 : ZMod q) ≠ 0)
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (hcollision :
      (∑ u : sizeTwoAllowedDifference q a,
        (sizeTwoCyclicTargetDifferenceMultiplicity code x t u).choose 2) = 1) :
    ∃ duplicate missing : sizeTwoAllowedDifference q a,
      duplicate ≠ missing ∧
      (∀ u : sizeTwoAllowedDifference q a,
        sizeTwoCyclicTargetDifferenceMultiplicity code x t u =
          if u = duplicate then 2 else if u = missing then 0 else 1) ∧
      ZMod.castHom (dvd_trans (by norm_num : 2 ∣ 4) h4q) (ZMod 2) duplicate.1 ≠
        ZMod.castHom (dvd_trans (by norm_num : 2 ∣ 4) h4q) (ZMod 2) missing.1 := by
  obtain ⟨duplicate, missing, hne, hprofile, hdisp⟩ :=
    exists_singleDuplicateMissing_displacement_of_collision_eq_one
      hq ha hq1 code x t hcollision
  exact ⟨duplicate, missing, hne, hprofile,
    sizeTwoCyclic_singleDuplicateMissing_parity_ne h4q hdisp⟩

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclic_singleDuplicateMissing_parity_ne
#print axioms
  Erdos85.sizeTwoCyclicTargetDifferenceMultiplicity_deviation_parity_eq_one
#print axioms Erdos85.existsUnique_paritySelectedAdjacentBase
#print axioms Erdos85.sizeTwoCyclicParitySlotColor_spec
#print axioms Erdos85.sizeTwoCyclicParitySlotColor_eq_of_spec
#print axioms
  Erdos85.exists_paritySeparated_duplicateMissing_of_collision_eq_one
