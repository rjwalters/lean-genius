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
#print axioms Erdos85.sizeTwoCyclicRouteLine_card_eq_multiplicity_diagonal_sum
#print axioms
  Erdos85.sizeTwoCyclicTargetDifferenceMultiplicity_diagonal_sum_even
