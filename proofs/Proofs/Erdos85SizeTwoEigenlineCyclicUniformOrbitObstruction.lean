import Proofs.Erdos85SizeTwoEigenlineCyclicPermutationDisplacementSum
import Proofs.Erdos85SizeTwoEigenlineCyclicMatchingSecondMomentCensus
import Proofs.Erdos85SizeTwoEigenlineCyclicMatchingReciprocity
import Proofs.Erdos85SizeTwoEigenlineCyclicMatchingCounts
import Proofs.Erdos85SizeTwoEigenlineCyclicFullOrbitRegularity
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Reciprocity obstructs uniform orbit multiplicity

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

The aggregate packing ledger admits the formal model in which every
difference orbit has multiplicity one at every allowed absolute cell.  That
model does not lift to a reciprocal routing code.  Reciprocity would make
every source matching hit every allowed target-difference fiber exactly
once, while the punctured-permutation displacement sum depends on the source
fiber.  Comparing the allowed source fibers `0` and `-1` gives `2 = 0`.
-/

namespace Erdos85

noncomputable section

private theorem allowedDifference_ne_reflection
    {q : ℕ} [NeZero q] (h2q : 2 ∣ q) (a : ZMod q) :
    a ≠ -1 - a := by
  intro ha
  have h := congrArg (ZMod.castHom h2q (ZMod 2)) ha
  have hone : ZMod.castHom h2q (ZMod 2) (1 : ZMod q) = 1 := map_one _
  have htwo : ZMod.castHom h2q (ZMod 2) (2 : ZMod q) = 0 := by
    simpa only [map_ofNat] using (show (2 : ZMod 2) = 0 by decide)
  rw [map_sub, map_neg, hone] at h
  have : ZMod.castHom h2q (ZMod 2) (2 * a) = 1 := by
    rw [map_mul, htwo, zero_mul]
    have := congrArg (fun z : ZMod 2 => z +
      ZMod.castHom h2q (ZMod 2) a) h
    simpa [sub_eq_add_neg, add_assoc] using this.symm
  rw [map_mul, htwo, zero_mul] at this
  exact zero_ne_one this

/-- A target source sees every source-difference orbit with multiplicity one. -/
def SizeTwoCyclicUniformIncidenceAt
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (target : SizeTwoCyclicMatchingSource q a) : Prop :=
  ∀ u : sizeTwoAllowedDifference q a,
    sizeTwoCyclicMatchingOrbitMultiplicity code u
      (sizeTwoCyclicMatchingSourceCell target) = 1

private theorem targetDifference_surjective_of_uniform
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) :
    SizeTwoCyclicUniformIncidenceAt code (x, t) →
    Function.Surjective
      (code.toReciprocalCode.targetDifference x t) := by
  intro huniform u
  have hcard := huniform u
  unfold sizeTwoCyclicMatchingOrbitMultiplicity at hcard
  have hpos : 0 < ((Finset.univ : Finset (ZMod q)).filter fun y =>
      sizeTwoCyclicMatchingSourceCell (x, t) ∈
        sizeTwoCyclicSourceMatching code (y, u)).card := by
    omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
  have hy' := (Finset.mem_filter.mp hy).2
  have hreverse : sizeTwoCyclicMatchingSourceCell (y, u) ∈
      sizeTwoCyclicSourceMatching code (x, t) :=
    (sizeTwoCyclicSourceMatching_sourceCell_mem_comm code (x, t) (y, u)).mpr hy'
  obtain ⟨r, hr⟩ :=
    (sizeTwoCyclicSourceMatching_mem_iff code (x, t)
      (sizeTwoCyclicMatchingSourceCell (y, u))).mp hreverse
  refine ⟨r, ?_⟩
  apply Subtype.ext
  have hfirst := congrArg Prod.fst hr
  have hsecond := congrArg Prod.snd hr
  have hcolumn := code.toReciprocalCode.target_column_eq x t r
  dsimp [sizeTwoCyclicMatchingEdge,
    sizeTwoCyclicMatchingSourceCell] at hfirst hsecond
  change r.1 + (code.toReciprocalCode.targetDifference x t r).1 =
    (code.toReciprocalCode.toPermutationCode.perm x t r).1 at hcolumn
  calc
    (code.toReciprocalCode.targetDifference x t r).1 =
        (x + (code.toReciprocalCode.toPermutationCode.perm x t r).1) -
          (x + r.1) := by rw [← hcolumn]; abel
    _ = (y + u.1) - y := by rw [hfirst, hsecond]
    _ = u.1 := by abel

private theorem targetDifference_bijective_of_uniform
    {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : a ≠ -1 - a) (hq1 : (1 : ZMod q) ≠ 0)
    (code : SizeTwoCyclicFullPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) :
    SizeTwoCyclicUniformIncidenceAt code (x, t) →
    Function.Bijective
      (code.toReciprocalCode.targetDifference x t) := by
  intro huniform
  apply (Fintype.bijective_iff_surjective_and_card _).2
  refine ⟨targetDifference_surjective_of_uniform code x t huniform, ?_⟩
  rw [sizeTwoAdmissibleTargetRow_card q t.1 hq1,
    sizeTwoAllowedDifference_card q a ha]

/-- Pointwise uniform incidence forces the allowed-fiber sum to equal the
affine displacement value attached to the target's own difference fiber. -/
theorem sizeTwoCyclicUniformIncidenceAt_fiberSum
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) {a : ZMod q}
    (ha : a ≠ -1 - a) (code : SizeTwoCyclicFullPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (huniform : SizeTwoCyclicUniformIncidenceAt code (x, t)) :
    (∑ u : sizeTwoAllowedDifference q a, u.1) = 2 * (t.1 + 1) := by
  have hq1 : (1 : ZMod q) ≠ 0 := by
    letI : Fact (1 < q) := ⟨hq⟩
    exact one_ne_zero
  let targetEquiv :
      SizeTwoAdmissibleTargetRow q t.1 ≃ sizeTwoAllowedDifference q a :=
    Equiv.ofBijective (code.toReciprocalCode.targetDifference x t)
      (targetDifference_bijective_of_uniform
        ha hq1 code x t huniform)
  calc
    (∑ u : sizeTwoAllowedDifference q a, u.1) =
        ∑ r : SizeTwoAdmissibleTargetRow q t.1,
          (code.toReciprocalCode.targetDifference x t r).1 := by
      exact (Equiv.sum_comp targetEquiv Subtype.val).symm
    _ = ∑ r : SizeTwoAdmissibleTargetRow q t.1,
        ((code.toReciprocalCode.toPermutationCode.perm x t r).1 - r.1) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hcolumn := code.toReciprocalCode.target_column_eq x t r
      exact eq_sub_of_add_eq (by simpa [add_comm] using hcolumn)
    _ = 2 * (t.1 + 1) :=
      sizeTwoCyclicPermutation_targetDifference_sum hq
        code.toReciprocalCode.toPermutationCode.perm x t

/-- Any two pointwise-uniform target rows lie in the same fiber of the
doubling endomorphism. -/
theorem two_mul_fiber_eq_of_uniformIncidenceAt
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) {a : ZMod q}
    (ha : a ≠ -1 - a) (code : SizeTwoCyclicFullPermutationCode q a)
    {x y : ZMod q} {t u : sizeTwoAllowedDifference q a}
    (ht : SizeTwoCyclicUniformIncidenceAt code (x, t))
    (hu : SizeTwoCyclicUniformIncidenceAt code (y, u)) :
    2 * t.1 = 2 * u.1 := by
  have hts := sizeTwoCyclicUniformIncidenceAt_fiberSum
    hq ha code x t ht
  have hus := sizeTwoCyclicUniformIncidenceAt_fiberSum
    hq ha code y u hu
  rw [hts] at hus
  linear_combination hus

/-- Difference fibers supporting at least one pointwise-uniform row. -/
def sizeTwoCyclicUniformIncidenceFibers
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a) :
    Finset (sizeTwoAllowedDifference q a) := by
  classical
  exact Finset.univ.filter fun t => ∃ x : ZMod q,
    SizeTwoCyclicUniformIncidenceAt code (x, t)

/-- For even `q`, at most two difference fibers can support a uniform row:
all such fibers lie in one fiber of doubling, whose kernel has cardinality
`gcd(q,2)=2`. -/
theorem sizeTwoCyclicUniformIncidenceFibers_card_le_two
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) (h2q : 2 ∣ q) {a : ZMod q}
    (ha : a ≠ -1 - a) (code : SizeTwoCyclicFullPermutationCode q a) :
    (sizeTwoCyclicUniformIncidenceFibers code).card ≤ 2 := by
  classical
  let U := sizeTwoCyclicUniformIncidenceFibers code
  by_cases hU : U.Nonempty
  · let t₀ : sizeTwoAllowedDifference q a := hU.choose
    have ht₀mem : t₀ ∈ U := hU.choose_spec
    have ht₀uniform : ∃ x : ZMod q,
        SizeTwoCyclicUniformIncidenceAt code (x, t₀) := by
      simpa [U, sizeTwoCyclicUniformIncidenceFibers] using ht₀mem
    let f : {t // t ∈ U} → (nsmulAddMonoidHom 2 : ZMod q →+ ZMod q).ker :=
      fun t => ⟨t.1.1 - t₀.1, by
        change 2 • (t.1.1 - t₀.1) = 0
        have htuniform : ∃ x : ZMod q,
            SizeTwoCyclicUniformIncidenceAt code (x, t.1) := by
          have hm : t.1 ∈ sizeTwoCyclicUniformIncidenceFibers code := by
            simp [U, t.2]
          rw [sizeTwoCyclicUniformIncidenceFibers] at hm
          exact (Finset.mem_filter.mp hm).2
        obtain ⟨x, hx⟩ := htuniform
        obtain ⟨x₀, hx₀⟩ := ht₀uniform
        have hdouble := two_mul_fiber_eq_of_uniformIncidenceAt
          hq ha code hx hx₀
        simpa [two_nsmul, sub_eq_add_neg] using
          congrArg (fun z : ZMod q => z - 2 * t₀.1) hdouble⟩
    have hf : Function.Injective f := by
      intro t u htu
      apply Subtype.ext
      apply Subtype.ext
      have hval := congrArg Subtype.val htu
      dsimp [f] at hval
      have hadd := congrArg (fun z : ZMod q => z + t₀.1) hval
      simpa [sub_eq_add_neg, add_assoc] using hadd
    calc
      U.card = Fintype.card {t // t ∈ U} := (Fintype.card_coe U).symm
      _ ≤ Fintype.card (nsmulAddMonoidHom 2 : ZMod q →+ ZMod q).ker :=
        Fintype.card_le_of_injective f hf
      _ = 2 := by
        rw [← Nat.card_eq_fintype_card,
          IsAddCyclic.card_nsmulAddMonoidHom_ker]
        simp [ZMod.card, Nat.gcd_eq_right_iff_dvd.mpr h2q]
  · simp [U, Finset.not_nonempty_iff_eq_empty.mp hU]

/-- Source rows whose vector of incident difference-orbit multiplicities is
not the all-ones vector. -/
def sizeTwoCyclicNonuniformIncidenceSources
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a) :
    Finset (SizeTwoCyclicMatchingSource q a) := by
  classical
  exact Finset.univ.filter fun target =>
    ¬SizeTwoCyclicUniformIncidenceAt code target

/-- Quantitative form of the reciprocity obstruction.  For even `q`, at
least `q(q-4)` source rows have a nonuniform incident-fiber vector: all rows
outside the at-most-two doubling fibers are nonuniform. -/
theorem sizeTwoCyclicNonuniformIncidenceSources_card_ge
    {q : ℕ} [NeZero q] (hq : 4 ≤ q) (h2q : 2 ∣ q) {a : ZMod q}
    (ha : a ≠ -1 - a) (code : SizeTwoCyclicFullPermutationCode q a) :
    q * (q - 4) ≤ (sizeTwoCyclicNonuniformIncidenceSources code).card := by
  classical
  let U := sizeTwoCyclicUniformIncidenceFibers code
  let B := sizeTwoCyclicNonuniformIncidenceSources code
  let forced : Finset (SizeTwoCyclicMatchingSource q a) :=
    (Finset.univ : Finset (ZMod q)) ×ˢ
      ((Finset.univ : Finset (sizeTwoAllowedDifference q a)) \ U)
  have hUcard : U.card ≤ 2 :=
    sizeTwoCyclicUniformIncidenceFibers_card_le_two
      (by omega) h2q ha code
  have hUsub : U ⊆ (Finset.univ : Finset (sizeTwoAllowedDifference q a)) :=
    Finset.subset_univ U
  have hforced : forced ⊆ B := by
    intro target htarget
    have htprod := Finset.mem_product.mp htarget
    have htU : target.2 ∉ U := (Finset.mem_sdiff.mp htprod.2).2
    change target ∈ sizeTwoCyclicNonuniformIncidenceSources code
    rw [sizeTwoCyclicNonuniformIncidenceSources, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro huniform
    apply htU
    change target.2 ∈ sizeTwoCyclicUniformIncidenceFibers code
    rw [sizeTwoCyclicUniformIncidenceFibers, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, target.1, huniform⟩
  have hcard := Finset.card_le_card hforced
  have hallowed : Fintype.card (sizeTwoAllowedDifference q a) = q - 2 :=
    sizeTwoAllowedDifference_card q a ha
  have hforcedCard : forced.card = q * ((q - 2) - U.card) := by
    change ((Finset.univ : Finset (ZMod q)) ×ˢ
      ((Finset.univ : Finset (sizeTwoAllowedDifference q a)) \ U)).card = _
    rw [Finset.card_product]
    rw [Finset.card_sdiff_of_subset hUsub]
    simp [ZMod.card, hallowed]
  rw [hforcedCard] at hcard
  change q * (q - 4) ≤ B.card
  have hsub : q - 4 ≤ (q - 2) - U.card := by omega
  exact (Nat.mul_le_mul_left q hsub).trans hcard

private theorem one_le_sum_choose_two_of_sum_eq_card_of_not_all_one
    {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hsum : (∑ i : ι, m i) = Fintype.card ι)
    (hnot : ¬∀ i, m i = 1) :
    1 ≤ ∑ i : ι, (m i).choose 2 := by
  classical
  by_contra hlt
  have hzero : (∑ i : ι, (m i).choose 2) = 0 := by omega
  have hpoint : ∀ i, (m i).choose 2 = 0 := by
    intro i
    have hle : (m i).choose 2 ≤ ∑ j : ι, (m j).choose 2 :=
      Finset.single_le_sum (s := Finset.univ)
        (f := fun j => (m j).choose 2)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hmle : ∀ i, m i ≤ 1 := by
    intro i
    have hi := hpoint i
    rw [Nat.choose_eq_zero_iff] at hi
    omega
  obtain ⟨i, hi⟩ := Classical.not_forall.mp hnot
  have hmi : m i = 0 := by
    have := hmle i
    omega
  have hsumle : (∑ j : ι, m j) ≤ Fintype.card ι - 1 := by
    rw [show (∑ j : ι, m j) =
        m i + ∑ j ∈ (Finset.univ : Finset ι).erase i, m j by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ i)]]
    rw [hmi, zero_add]
    calc
      (∑ j ∈ (Finset.univ : Finset ι).erase i, m j) ≤
          ∑ _j ∈ (Finset.univ : Finset ι).erase i, 1 := by
        apply Finset.sum_le_sum
        intro j hj
        exact hmle j
      _ = Fintype.card ι - 1 := by simp
  rw [hsum] at hsumle
  have hcardpos : 0 < Fintype.card ι :=
    Fintype.card_pos_iff.mpr ⟨i⟩
  omega

/-- Collision mass of the incident-fiber multiplicity vector, summed over
all source rows.  By incidence transpose this is the within-orbit collision
mass restricted to allowed absolute cells. -/
def sizeTwoCyclicIncidenceCollisionMass
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a) : ℕ :=
  ∑ target : SizeTwoCyclicMatchingSource q a,
    ∑ u : sizeTwoAllowedDifference q a,
      (sizeTwoCyclicMatchingOrbitMultiplicity code u
        (sizeTwoCyclicMatchingSourceCell target)).choose 2

theorem one_le_sizeTwoCyclicIncidenceCollisionRow_of_nonuniform
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) {a : ZMod q}
    (ha : a ≠ -1 - a) (code : SizeTwoCyclicFullPermutationCode q a)
    (target : SizeTwoCyclicMatchingSource q a)
    (hbad : ¬SizeTwoCyclicUniformIncidenceAt code target) :
    1 ≤ ∑ u : sizeTwoAllowedDifference q a,
      (sizeTwoCyclicMatchingOrbitMultiplicity code u
        (sizeTwoCyclicMatchingSourceCell target)).choose 2 := by
  have hq1 : (1 : ZMod q) ≠ 0 := by
    letI : Fact (1 < q) := ⟨hq⟩
    exact one_ne_zero
  apply one_le_sum_choose_two_of_sum_eq_card_of_not_all_one
  · have hfull := sizeTwoCyclicFullOrbitMultiplicity_sourceCell_eq_sub_two
      code hq1 target
    unfold sizeTwoCyclicSelectedOrbitMultiplicity at hfull
    rw [sizeTwoAllowedDifference_card q a ha]
    simpa using hfull
  · exact hbad

/-- Every nonuniform source row contributes at least one within-orbit
collision, so the quantitative row obstruction lower-bounds total incidence
collision mass. -/
theorem sizeTwoCyclicNonuniformIncidenceSources_card_le_collisionMass
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) {a : ZMod q}
    (ha : a ≠ -1 - a) (code : SizeTwoCyclicFullPermutationCode q a) :
    (sizeTwoCyclicNonuniformIncidenceSources code).card ≤
      sizeTwoCyclicIncidenceCollisionMass code := by
  classical
  rw [show (sizeTwoCyclicNonuniformIncidenceSources code).card =
      ∑ target : SizeTwoCyclicMatchingSource q a,
        if ¬SizeTwoCyclicUniformIncidenceAt code target then 1 else 0 by
    rw [sizeTwoCyclicNonuniformIncidenceSources, Finset.card_filter]]
  unfold sizeTwoCyclicIncidenceCollisionMass
  apply Finset.sum_le_sum
  intro target htarget
  by_cases hbad : ¬SizeTwoCyclicUniformIncidenceAt code target
  · rw [if_pos hbad]
    exact one_le_sizeTwoCyclicIncidenceCollisionRow_of_nonuniform
      hq ha code target hbad
  · rw [if_neg hbad]
    exact Nat.zero_le _

/-- q-generic quantitative reciprocity obstruction: for every even `q≥4`,
the within-orbit incidence collision mass is at least `q(q-4)`. -/
theorem sizeTwoCyclicIncidenceCollisionMass_ge
    {q : ℕ} [NeZero q] (hq : 4 ≤ q) (h2q : 2 ∣ q) {a : ZMod q}
    (ha : a ≠ -1 - a) (code : SizeTwoCyclicFullPermutationCode q a) :
    q * (q - 4) ≤ sizeTwoCyclicIncidenceCollisionMass code :=
  (sizeTwoCyclicNonuniformIncidenceSources_card_ge
    hq h2q ha code).trans
      (sizeTwoCyclicNonuniformIncidenceSources_card_le_collisionMass
        (by omega) ha code)

/-- The incidence collision mass is a restriction of the standard sum of
within-orbit collision masses to source cells, hence is no larger than that
full absolute-grid sum. -/
theorem sizeTwoCyclicIncidenceCollisionMass_le_withinOrbitCollisionMass
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a) :
    sizeTwoCyclicIncidenceCollisionMass code ≤
      ∑ u : sizeTwoAllowedDifference q a,
        ∑ e : SizeTwoCyclicAbsoluteGridEdge q,
          (sizeTwoCyclicMatchingOrbitMultiplicity code u e).choose 2 := by
  classical
  unfold sizeTwoCyclicIncidenceCollisionMass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro u hu
  let sourceCells : Finset (SizeTwoCyclicAbsoluteGridEdge q) :=
    (Finset.univ : Finset (SizeTwoCyclicMatchingSource q a)).image
      sizeTwoCyclicMatchingSourceCell
  have himage :
      (∑ e ∈ sourceCells,
        (sizeTwoCyclicMatchingOrbitMultiplicity code u e).choose 2) =
      ∑ target : SizeTwoCyclicMatchingSource q a,
        (sizeTwoCyclicMatchingOrbitMultiplicity code u
          (sizeTwoCyclicMatchingSourceCell target)).choose 2 := by
    apply Finset.sum_image
    exact sizeTwoCyclicMatchingSourceCell_injective.injOn
  rw [← himage]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ sourceCells)

/-- Standard within-orbit form of the quantitative reciprocity obstruction. -/
theorem sizeTwoCyclicWithinOrbitCollisionMass_ge
    {q : ℕ} [NeZero q] (hq : 4 ≤ q) (h2q : 2 ∣ q) {a : ZMod q}
    (ha : a ≠ -1 - a) (code : SizeTwoCyclicFullPermutationCode q a) :
    q * (q - 4) ≤
      ∑ u : sizeTwoAllowedDifference q a,
        ∑ e : SizeTwoCyclicAbsoluteGridEdge q,
          (sizeTwoCyclicMatchingOrbitMultiplicity code u e).choose 2 :=
  (sizeTwoCyclicIncidenceCollisionMass_ge hq h2q ha code).trans
    (sizeTwoCyclicIncidenceCollisionMass_le_withinOrbitCollisionMass code)

/-- A reciprocal full code cannot realize the aggregate uniform model in
which every difference-orbit multiplicity is one at every absolute cell. -/
theorem not_binary_sizeTwoCyclic_uniformOrbitMultiplicity
    {q : ℕ} [NeZero q] (hq : 4 ≤ q) (h2q : 2 ∣ q)
    {a : ZMod q} (ha0 : a ≠ 0) (ha1 : a ≠ -1)
    (code : SizeTwoCyclicFullPermutationCode q a) :
    ¬(∀ (t : sizeTwoAllowedDifference q a)
      (e : SizeTwoCyclicAbsoluteGridEdge q),
      sizeTwoCyclicMatchingOrbitMultiplicity code t e = 1) := by
  intro huniform
  have hq1 : (1 : ZMod q) ≠ 0 := by
    letI : Fact (1 < q) := ⟨by omega⟩
    exact one_ne_zero
  have hq2 : (2 : ZMod q) ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    have hv' : 2 % q = 0 := by
      simpa [ZMod.val_ofNat] using hv
    rw [Nat.mod_eq_of_lt (by omega)] at hv'
    omega
  have harefl : a ≠ -1 - a := allowedDifference_ne_reflection h2q a
  let zeroFiber : sizeTwoAllowedDifference q a :=
    ⟨0, ha0.symm, by
      intro h
      apply ha1
      have := congrArg (fun z : ZMod q => -1 - z) h
      simpa [sub_eq_add_neg, add_assoc] using this.symm⟩
  let negOneFiber : sizeTwoAllowedDifference q a :=
    ⟨-1, ha1.symm, by
      intro h
      apply ha0
      have := congrArg (fun z : ZMod q => z + 1) h
      simpa [sub_eq_add_neg, add_assoc] using this.symm⟩
  have fiberSum (x : ZMod q) (t : sizeTwoAllowedDifference q a) :
      (∑ u : sizeTwoAllowedDifference q a, u.1) = 2 * (t.1 + 1) := by
    apply sizeTwoCyclicUniformIncidenceAt_fiberSum (by omega) harefl code x t
    intro u
    exact huniform u (sizeTwoCyclicMatchingSourceCell (x, t))
  have hz := fiberSum 0 zeroFiber
  have hn := fiberSum 0 negOneFiber
  apply hq2
  calc
    (2 : ZMod q) = 2 * (zeroFiber.1 + 1) := by simp [zeroFiber]
    _ = ∑ u : sizeTwoAllowedDifference q a, u.1 := hz.symm
    _ = 2 * (negOneFiber.1 + 1) := hn
    _ = 0 := by simp [negOneFiber]

end

end Erdos85

#print axioms Erdos85.not_binary_sizeTwoCyclic_uniformOrbitMultiplicity
#print axioms Erdos85.sizeTwoCyclicUniformIncidenceFibers_card_le_two
#print axioms Erdos85.sizeTwoCyclicNonuniformIncidenceSources_card_ge
#print axioms Erdos85.sizeTwoCyclicWithinOrbitCollisionMass_ge
