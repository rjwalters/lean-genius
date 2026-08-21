import Proofs.Erdos85SizeTwoEigenlineCyclicCanonicalReflectionPermutation
import Proofs.Erdos85SizeTwoEigenlineCyclicRouteReversalSign

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

noncomputable instance SizeTwoCyclicRouteLine.instFintype
    (q : ℕ) [NeZero q] (a : ZMod q)
    (code : SizeTwoCyclicReciprocalPermutationCode q a) (ell : ZMod q) :
    Fintype (SizeTwoCyclicRouteLine q a code ell) := by
  letI := SizeTwoCyclicRouteDart.instFintype q a code
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Reversal restricted to one line-label fibre. -/
def sizeTwoCyclicRouteLineReverse
    {q : ℕ} [NeZero q] {a : ZMod q}
    {code : SizeTwoCyclicReciprocalPermutationCode q a} {ell : ZMod q}
    (e : SizeTwoCyclicRouteLine q a code ell) :
    SizeTwoCyclicRouteLine q a code ell :=
  ⟨e.1.reverse, by rw [e.1.lineLabel_reverse, e.2]⟩

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

end

end Erdos85

#print axioms Erdos85.SizeTwoCyclicRouteDart.lineLabel_eq_reflected
#print axioms Erdos85.SizeTwoCyclicRouteDart.lineLabel_reverse
#print axioms Erdos85.sizeTwoCyclicRouteLine_card_even
