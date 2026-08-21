import Proofs.Erdos85SizeTwoEigenlineCyclicCanonicalReflectionPermutation
import Proofs.Erdos85SizeTwoEigenlineCyclicTargetFiberReciprocity

/-!
# Line-resolved parity of cyclic route reversal

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3.

Global route-reversal parity loses the base/fiber grading.  The grading that
reversal actually preserves is the sum of the source and target differences.
In reflected coordinates it is

`t + s = 2*t - r - rho_(x,t)(r)`.

Thus every line-label fibre, not merely the full dart space, is paired by
fixed-point-free reversal and has even cardinality.  This is the first
genuinely line-resolved parity constraint on the reflected permutations.
-/

namespace Erdos85

noncomputable section

/-- The reversal-invariant line label of a routed dart: source difference
plus target difference. -/
def SizeTwoCyclicRouteDart.lineLabel
    {q : ℕ} [NeZero q] {a : ZMod q}
    {code : SizeTwoCyclicReciprocalPermutationCode q a}
    (e : SizeTwoCyclicRouteDart q a code) : ZMod q :=
  let x := e.1.1
  let t := e.1.2.1
  let r : SizeTwoAdmissibleTargetRow q t.1 := ⟨e.1.2.2, e.2⟩
  t.1 + (code.targetDifference x t r).1

/-- In reflected coordinates the line label is `2t-r-rho(r)`. -/
theorem SizeTwoCyclicRouteDart.lineLabel_eq_reflected
    {q : ℕ} [NeZero q] {a : ZMod q}
    {code : SizeTwoCyclicReciprocalPermutationCode q a}
    (e : SizeTwoCyclicRouteDart q a code) :
    e.lineLabel =
      2 * e.1.2.1.1 - e.1.2.2 -
        (code.reflectedPerm e.1.1 e.1.2.1
          ⟨e.1.2.2, e.2⟩).1 := by
  rw [code.reflectedPerm_val]
  rcases e with ⟨⟨x, t, r⟩, hr⟩
  simp only [SizeTwoCyclicRouteDart.lineLabel]
  have hcol := code.target_column_eq x t ⟨r, hr⟩
  change r + (code.targetDifference x t ⟨r, hr⟩).1 =
    (code.toPermutationCode.perm x t ⟨r, hr⟩).1 at hcol
  rw [← hcol]
  ring

/-- Route reversal preserves the line label. -/
theorem SizeTwoCyclicRouteDart.lineLabel_reverse
    {q : ℕ} [NeZero q] {a : ZMod q}
    {code : SizeTwoCyclicReciprocalPermutationCode q a}
    (e : SizeTwoCyclicRouteDart q a code) :
    e.reverse.lineLabel = e.lineLabel := by
  rcases e with ⟨⟨x, t, r⟩, hr⟩
  simp only [SizeTwoCyclicRouteDart.lineLabel,
    SizeTwoCyclicRouteDart.reverse]
  rw [show code.targetDifference
      (x + r) (code.targetDifference x t ⟨r, hr⟩)
        ⟨-r, code.reverse_admissible x t ⟨r, hr⟩⟩ = t from
    code.reverse_targetDifference x t ⟨r, hr⟩]
  exact add_comm _ _

/-- Routed darts on a fixed reversal-invariant line. -/
def SizeTwoCyclicRouteLine
    (q : ℕ) [NeZero q] (a : ZMod q)
    (code : SizeTwoCyclicReciprocalPermutationCode q a) (ell : ZMod q) :=
  {e : SizeTwoCyclicRouteDart q a code // e.lineLabel = ell}

/-- Allowed target differences lying on line `ell` with source difference
`t`. -/
abbrev SizeTwoAllowedLineTarget
    (q : ℕ) [NeZero q] (a : ZMod q)
    (t : sizeTwoAllowedDifference q a) (ell : ZMod q) :=
  {u : sizeTwoAllowedDifference q a // t.1 + u.1 = ell}

noncomputable instance SizeTwoCyclicRouteLine.instFintype
    (q : ℕ) [NeZero q] (a : ZMod q)
    (code : SizeTwoCyclicReciprocalPermutationCode q a) (ell : ZMod q) :
    Fintype (SizeTwoCyclicRouteLine q a code ell) := by
  letI := SizeTwoCyclicRouteDart.instFintype code
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Reversal restricted to one line-label fibre. -/
def sizeTwoCyclicRouteLineReverse
    {q : ℕ} [NeZero q] {a : ZMod q}
    {code : SizeTwoCyclicReciprocalPermutationCode q a} {ell : ZMod q}
    (e : SizeTwoCyclicRouteLine q a code ell) :
    SizeTwoCyclicRouteLine q a code ell :=
  ⟨e.1.reverse, by rw [e.1.lineLabel_reverse, e.2]⟩

/-- Decompose a line fibre into its ordered source/target difference
blocks.  This is the bridge from line parity to the existing multiplicity
matrix. -/
def sizeTwoCyclicRouteLineEquivFiberPairs
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a) (ell : ZMod q) :
    SizeTwoCyclicRouteLine q a code ell ≃
      Σ t : sizeTwoAllowedDifference q a,
        Σ u : SizeTwoAllowedLineTarget q a t ell,
          SizeTwoCyclicTargetFiberRoute code t u.1 where
  toFun p := by
    let e := p.1
    let x := e.1.1
    let t := e.1.2.1
    let r : SizeTwoAdmissibleTargetRow q t.1 := ⟨e.1.2.2, e.2⟩
    let u := code.targetDifference x t r
    refine ⟨t, ⟨u, ?_⟩, ⟨e, rfl, rfl⟩⟩
    exact p.2
  invFun p := by
    rcases p with ⟨t, ⟨u, hline⟩, ⟨e, hsource, htarget⟩⟩
    refine ⟨e, ?_⟩
    rcases e with ⟨⟨x, s, r⟩, hr⟩
    change s = t at hsource
    subst s
    change code.targetDifference x t ⟨r, hr⟩ = u at htarget
    change t.1 + (code.targetDifference x t ⟨r, hr⟩).1 = ell
    rw [htarget]
    exact hline
  left_inv p := by
    rcases p with ⟨⟨⟨x, t, r⟩, hr⟩, hline⟩
    rfl
  right_inv p := by
    rcases p with ⟨t, ⟨u, hline⟩, ⟨⟨⟨x, s, r⟩, hr⟩,
      hsource, htarget⟩⟩
    change s = t at hsource
    subst s
    change code.targetDifference x t ⟨r, hr⟩ = u at htarget
    subst u
    rfl

/-- Exact diagonal-sum formula for a line fibre. -/
theorem sizeTwoCyclicRouteLine_card_eq_multiplicity_diagonal_sum
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a) (ell : ZMod q) :
    Fintype.card (SizeTwoCyclicRouteLine q a code ell) =
      ∑ t : sizeTwoAllowedDifference q a,
        ∑ u : SizeTwoAllowedLineTarget q a t ell,
          ∑ x : ZMod q,
            sizeTwoCyclicTargetDifferenceMultiplicity code x t u.1 := by
  rw [Fintype.card_congr (sizeTwoCyclicRouteLineEquivFiberPairs code ell),
    Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro u _
  exact sizeTwoCyclicTargetFiberRoute_card_eq_multiplicity_sum code t u.1

/-- Every line-label fibre has even size when the routing code is loopless. -/
theorem sizeTwoCyclicRouteLine_card_even
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (hloop : code.Loopless) (ell : ZMod q) :
    Even (Fintype.card (SizeTwoCyclicRouteLine q a code ell)) := by
  classical
  let sigma := sizeTwoCyclicRouteLineReverse
    (q := q) (a := a) (code := code) (ell := ell)
  have hinv : Function.Involutive sigma := by
    intro e
    apply Subtype.ext
    exact e.1.reverse_reverse
  have hfree : ∀ e, sigma e ≠ e := by
    intro e he
    apply e.1.reverse_ne hloop
    exact congrArg Subtype.val he
  have hsum :
      (∑ _e : SizeTwoCyclicRouteLine q a code ell, (1 : ZMod 2)) = 0 := by
    apply Finset.sum_ninvolution sigma
    · intro e
      decide
    · intro e _
      exact hfree e
    · intro e
      exact Finset.mem_univ _
    · intro e
      exact hinv e
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hsum
  rwa [ZMod.natCast_eq_zero_iff_even] at hsum

/-- The diagonal block from a difference fibre back to itself is even:
loopless reversal pairs its routes internally. -/
theorem sizeTwoCyclicTargetFiberRoute_self_card_even
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (hloop : code.Loopless) (t : sizeTwoAllowedDifference q a) :
    Even (Fintype.card (SizeTwoCyclicTargetFiberRoute code t t)) := by
  classical
  let sigma : SizeTwoCyclicTargetFiberRoute code t t →
      SizeTwoCyclicTargetFiberRoute code t t :=
    sizeTwoCyclicTargetFiberRouteReverseEquiv code t t
  have hinv : Function.Involutive sigma := by
    intro e
    apply Subtype.ext
    exact e.1.reverse_reverse
  have hfree : ∀ e, sigma e ≠ e := by
    intro e he
    apply e.1.reverse_ne hloop
    exact congrArg Subtype.val he
  have hsum :
      (∑ _e : SizeTwoCyclicTargetFiberRoute code t t, (1 : ZMod 2)) = 0 := by
    apply Finset.sum_ninvolution sigma
    · intro e
      decide
    · intro e _
      exact hfree e
    · intro e
      exact Finset.mem_univ _
    · intro e
      exact hinv e
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hsum
  rwa [ZMod.natCast_eq_zero_iff_even] at hsum

/-- In multiplicity coordinates, the aggregate number of routes returning
to any fixed difference fibre is even. -/
theorem sizeTwoCyclicTargetDifferenceMultiplicity_self_sum_even
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (hloop : code.Loopless) (t : sizeTwoAllowedDifference q a) :
    Even (∑ x : ZMod q,
      sizeTwoCyclicTargetDifferenceMultiplicity code x t t) := by
  rw [← sizeTwoCyclicTargetFiberRoute_card_eq_multiplicity_sum code t t]
  exact sizeTwoCyclicTargetFiberRoute_self_card_even code hloop t

/-- In a sharp one-duplicate/one-missing profile over an even number of
bases, every target fibre is duplicated and missed equally modulo two.
This is the sharp-profile content of diagonal route parity. -/
theorem sizeTwoCyclicSharpProfile_selfDuplicate_modEq_selfMissing
    {q : ℕ} [NeZero q] {a : ZMod q}
    [DecidableEq (sizeTwoAllowedDifference q a)]
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (hloop : code.Loopless) (hqEven : Even q)
    (duplicate missing : ZMod q → sizeTwoAllowedDifference q a →
      sizeTwoAllowedDifference q a)
    (hne : ∀ x t, duplicate x t ≠ missing x t)
    (hprofile : ∀ x t u,
      sizeTwoCyclicTargetDifferenceMultiplicity code x t u =
        if u = duplicate x t then 2
        else if u = missing x t then 0 else 1)
    (t : sizeTwoAllowedDifference q a) :
    ((Finset.univ : Finset (ZMod q)).filter
        fun x => duplicate x t = t).card ≡
      ((Finset.univ : Finset (ZMod q)).filter
        fun x => missing x t = t).card [MOD 2] := by
  classical
  let D := (Finset.univ : Finset (ZMod q)).filter
    fun x => duplicate x t = t
  let M := (Finset.univ : Finset (ZMod q)).filter
    fun x => missing x t = t
  have hsumEven :=
    sizeTwoCyclicTargetDifferenceMultiplicity_self_sum_even code hloop t
  have hsumZero :
      ((∑ x : ZMod q,
        sizeTwoCyclicTargetDifferenceMultiplicity code x t t : ℕ) :
          ZMod 2) = 0 :=
    ZMod.natCast_eq_zero_iff_even.mpr hsumEven
  have hqZero : (q : ZMod 2) = 0 :=
    ZMod.natCast_eq_zero_iff_even.mpr hqEven
  have hcount :
      ((∑ x : ZMod q,
        sizeTwoCyclicTargetDifferenceMultiplicity code x t t : ℕ) :
          ZMod 2) = (q : ZMod 2) + (D.card : ZMod 2) + M.card := by
    rw [Nat.cast_sum]
    simp only [hprofile, Nat.cast_ite, Nat.cast_ofNat]
    calc
      (∑ x : ZMod q,
          (if t = duplicate x t then (2 : ZMod 2)
            else if t = missing x t then 0 else 1)) =
          ∑ x : ZMod q,
            (1 + (if duplicate x t = t then 1 else 0) +
              (if missing x t = t then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hd : duplicate x t = t
        · have hm : missing x t ≠ t := by
            intro hm
            apply hne x t
            exact hd.trans hm.symm
          have htd : t = duplicate x t := hd.symm
          have htm : t ≠ missing x t := fun h => hm h.symm
          rw [if_pos htd, if_pos hd, if_neg hm]
          decide
        · have hdt : t ≠ duplicate x t := fun h => hd h.symm
          by_cases hm : missing x t = t
          · have hmt : t = missing x t := hm.symm
            rw [if_neg hdt, if_pos hmt, if_neg hd, if_pos hm]
            decide
          · have hmt : t ≠ missing x t := fun h => hm h.symm
            rw [if_neg hdt, if_neg hmt, if_neg hd, if_neg hm]
            simp only [add_zero]
      _ = (q : ZMod 2) + (D.card : ZMod 2) + M.card := by
        simp only [Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, mul_one, Finset.sum_boole,
          ZMod.card]
        rfl
  have hDM : (D.card : ZMod 2) = (M.card : ZMod 2) := by
    rw [hqZero] at hcount
    rw [hsumZero] at hcount
    have hzero : (0 : ZMod 2) = D.card + M.card := by
      simpa only [zero_add] using hcount
    calc
      (D.card : ZMod 2) = D.card + 0 := (add_zero _).symm
      _ = D.card + (D.card + M.card) := by rw [← hzero]
      _ = (D.card + D.card : ZMod 2) + M.card := by rw [add_assoc]
      _ = M.card := by rw [CharTwo.add_self_eq_zero, zero_add]
  exact (ZMod.natCast_eq_natCast_iff D.card M.card 2).mp hDM

/-- The target-difference multiplicity matrix has even sum on every affine
anti-diagonal `t+u=ell`. -/
theorem sizeTwoCyclicTargetDifferenceMultiplicity_diagonal_sum_even
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (hloop : code.Loopless) (ell : ZMod q) :
    Even (∑ t : sizeTwoAllowedDifference q a,
      ∑ u : SizeTwoAllowedLineTarget q a t ell,
        ∑ x : ZMod q,
          sizeTwoCyclicTargetDifferenceMultiplicity code x t u.1) := by
  rw [← sizeTwoCyclicRouteLine_card_eq_multiplicity_diagonal_sum code ell]
  exact sizeTwoCyclicRouteLine_card_even code hloop ell

end

end Erdos85

#print axioms Erdos85.SizeTwoCyclicRouteDart.lineLabel_eq_reflected
#print axioms Erdos85.SizeTwoCyclicRouteDart.lineLabel_reverse
#print axioms Erdos85.sizeTwoCyclicRouteLine_card_even
#print axioms Erdos85.sizeTwoCyclicTargetFiberRoute_self_card_even
#print axioms
  Erdos85.sizeTwoCyclicTargetDifferenceMultiplicity_self_sum_even
#print axioms
  Erdos85.sizeTwoCyclicSharpProfile_selfDuplicate_modEq_selfMissing
#print axioms Erdos85.sizeTwoCyclicRouteLine_card_eq_multiplicity_diagonal_sum
#print axioms
  Erdos85.sizeTwoCyclicTargetDifferenceMultiplicity_diagonal_sum_even
