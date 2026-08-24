import Proofs.Erdos85SizeTwoEigenlineCyclicTargetFiberReciprocity

/-!
# Base-resolved cyclic route reciprocity

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

Aggregate sharp-defect counts admit countermodels.  Here we retain the base
points at both ends.  The resulting four-index incidence tensor is `0/1`,
transposes exactly under route reversal, and has the earlier local
target-fiber multiplicities as its row sums.
-/

namespace Erdos85

noncomputable section

/-- Relative rows routing the precise source cell `(x,t)` to the precise
target cell `(y,u)`. -/
def SizeTwoCyclicBaseResolvedRoute
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (y : ZMod q) (u : sizeTwoAllowedDifference q a) :=
  {r : SizeTwoAdmissibleTargetRow q t.1 //
    x + r.1 = y ∧ code.targetDifference x t r = u}

instance SizeTwoCyclicBaseResolvedRoute.instFinite
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (y : ZMod q) (u : sizeTwoAllowedDifference q a) :
    Finite (SizeTwoCyclicBaseResolvedRoute code x t y u) :=
  Finite.of_injective (fun r => r.1.1) (by
    intro r s h
    apply Subtype.ext
    exact Subtype.ext h)

noncomputable instance SizeTwoCyclicBaseResolvedRoute.instFintype
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (y : ZMod q) (u : sizeTwoAllowedDifference q a) :
    Fintype (SizeTwoCyclicBaseResolvedRoute code x t y u) := by
  exact Fintype.ofFinite _

/-- A base-resolved route is unique: its row is forced to be `y-x`. -/
theorem sizeTwoCyclicBaseResolvedRoute_card_le_one
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (y : ZMod q) (u : sizeTwoAllowedDifference q a) :
    Fintype.card (SizeTwoCyclicBaseResolvedRoute code x t y u) ≤ 1 := by
  classical
  rw [Fintype.card_le_one_iff]
  intro p w
  apply Subtype.ext
  apply Subtype.ext
  calc
    p.1.1 = -x + (x + p.1.1) := by abel
    _ = -x + y := by rw [p.2.1]
    _ = -x + (x + w.1.1) := by rw [w.2.1]
    _ = w.1.1 := by abel

/-- Reverse a route while retaining both endpoint coordinates. -/
def sizeTwoCyclicBaseResolvedRouteReverse
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (y : ZMod q) (u : sizeTwoAllowedDifference q a) :
    SizeTwoCyclicBaseResolvedRoute code x t y u →
      SizeTwoCyclicBaseResolvedRoute code y u x t := by
  intro p
  rcases p with ⟨r, hy, hu⟩
  subst u
  let reverseRow : SizeTwoAdmissibleTargetRow q
      (code.targetDifference x t r).1 :=
    ⟨-r.1, code.reverse_admissible x t r⟩
  refine ⟨reverseRow, ?_, ?_⟩
  · dsimp [reverseRow]
    rw [← hy]
    abel
  · rw [← hy]
    exact code.reverse_targetDifference x t r

/-- Exact transpose symmetry of the base-resolved `0/1` tensor. -/
theorem sizeTwoCyclicBaseResolvedRoute_card_symm
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (y : ZMod q) (u : sizeTwoAllowedDifference q a) :
    Fintype.card (SizeTwoCyclicBaseResolvedRoute code x t y u) =
      Fintype.card (SizeTwoCyclicBaseResolvedRoute code y u x t) := by
  apply Nat.le_antisymm
  · apply Fintype.card_le_of_injective
      (sizeTwoCyclicBaseResolvedRouteReverse code x t y u)
    intro p w _
    exact (Fintype.card_le_one_iff.mp
      (sizeTwoCyclicBaseResolvedRoute_card_le_one code x t y u)) p w
  · apply Fintype.card_le_of_injective
      (sizeTwoCyclicBaseResolvedRouteReverse code y u x t)
    intro p w _
    exact (Fintype.card_le_one_iff.mp
      (sizeTwoCyclicBaseResolvedRoute_card_le_one code y u x t)) p w

/-- Summing over the target base recovers the local target-difference
multiplicity. -/
theorem sizeTwoCyclicBaseResolvedRoute_card_sum
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t u : sizeTwoAllowedDifference q a) :
    (∑ y : ZMod q,
      Fintype.card (SizeTwoCyclicBaseResolvedRoute code x t y u)) =
        sizeTwoCyclicTargetDifferenceMultiplicity code x t u := by
  classical
  let Routes := Σ y : ZMod q,
    SizeTwoCyclicBaseResolvedRoute code x t y u
  let Local := {r : SizeTwoAdmissibleTargetRow q t.1 //
    code.targetDifference x t r = u}
  let e : Routes ≃ Local := {
    toFun := fun p => ⟨p.2.1, p.2.2.2⟩
    invFun := fun r => ⟨x + r.1.1, ⟨r.1, rfl, r.2⟩⟩
    left_inv := fun p => by
      rcases p with ⟨y, r, hy, hu⟩
      subst y
      rfl
    right_inv := fun r => by rfl }
  calc
    _ = Fintype.card Routes := (Fintype.card_sigma).symm
    _ = Fintype.card Local := Fintype.card_congr e
    _ = sizeTwoCyclicTargetDifferenceMultiplicity code x t u := by
      unfold sizeTwoCyclicTargetDifferenceMultiplicity
      rw [Fintype.card_subtype, Finset.card_filter]

/-- Pointwise, not merely aggregate, reciprocity: the incoming degree of the
target cell `(y,u)` from difference fiber `t` equals its reverse local
multiplicity into `t`.  Thus every `q × q` base block has the two sharp local
profiles as its row- and column-degree sequences. -/
theorem sizeTwoCyclicBaseResolvedRoute_card_column_sum
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (y : ZMod q) (u t : sizeTwoAllowedDifference q a) :
    (∑ x : ZMod q,
      Fintype.card (SizeTwoCyclicBaseResolvedRoute code x t y u)) =
        sizeTwoCyclicTargetDifferenceMultiplicity code y u t := by
  calc
    _ = ∑ x : ZMod q,
        Fintype.card (SizeTwoCyclicBaseResolvedRoute code y u x t) := by
      apply Finset.sum_congr rfl
      intro x _
      exact sizeTwoCyclicBaseResolvedRoute_card_symm code x t y u
    _ = sizeTwoCyclicTargetDifferenceMultiplicity code y u t :=
      sizeTwoCyclicBaseResolvedRoute_card_sum code y u t

/-- The fiber blocks are not independent.  For a fixed source cell and
target base, exactly one target-difference block contains the route when the
relative row is admissible, and none does at either moving hole. -/
theorem sizeTwoCyclicBaseResolvedRoute_card_sum_targetDifferences
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x y : ZMod q) (t : sizeTwoAllowedDifference q a) :
    (∑ u : sizeTwoAllowedDifference q a,
      Fintype.card (SizeTwoCyclicBaseResolvedRoute code x t y u)) =
        if t.1 ≠ y - x ∧ t.1 ≠ (y - x) - 1 then 1 else 0 := by
  classical
  let Routes := Σ u : sizeTwoAllowedDifference q a,
    SizeTwoCyclicBaseResolvedRoute code x t y u
  let Rows := {r : SizeTwoAdmissibleTargetRow q t.1 // x + r.1 = y}
  let e : Routes ≃ Rows := {
    toFun := fun p => ⟨p.2.1, p.2.2.1⟩
    invFun := fun r =>
      ⟨code.targetDifference x t r.1, ⟨r.1, r.2, rfl⟩⟩
    left_inv := fun p => by
      rcases p with ⟨u, r, hy, hu⟩
      subst u
      rfl
    right_inv := fun r => by rfl }
  rw [show (∑ u : sizeTwoAllowedDifference q a,
      Fintype.card (SizeTwoCyclicBaseResolvedRoute code x t y u)) =
        Fintype.card Routes from (Fintype.card_sigma).symm,
    Fintype.card_congr e]
  by_cases h : t.1 ≠ y - x ∧ t.1 ≠ (y - x) - 1
  · rw [if_pos h]
    let r0 : Rows := ⟨⟨y - x, h⟩, by
      change x + (y - x) = y
      abel⟩
    letI : Unique Rows := {
      default := r0
      uniq := by
        intro r
        apply Subtype.ext
        apply Subtype.ext
        calc
          r.1.1 = -x + (x + r.1.1) := by abel
          _ = -x + y := by rw [r.2]
          _ = y - x := by abel }
    exact Fintype.card_unique
  · rw [if_neg h]
    haveI : IsEmpty Rows := ⟨by
      intro r
      apply h
      have rval : r.1.1 = y - x := by
        calc
          r.1.1 = -x + (x + r.1.1) := by abel
          _ = -x + y := by rw [r.2]
          _ = y - x := by abel
      simpa [rval] using r.1.2⟩
    exact Fintype.card_eq_zero

/-- The transposed partition law: fixing the two bases and the target
difference also selects exactly one source-difference fiber away from the
two reverse moving holes. -/
theorem sizeTwoCyclicBaseResolvedRoute_card_sum_sourceDifferences
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x y : ZMod q) (u : sizeTwoAllowedDifference q a) :
    (∑ t : sizeTwoAllowedDifference q a,
      Fintype.card (SizeTwoCyclicBaseResolvedRoute code x t y u)) =
        if u.1 ≠ x - y ∧ u.1 ≠ (x - y) - 1 then 1 else 0 := by
  calc
    _ = ∑ t : sizeTwoAllowedDifference q a,
        Fintype.card (SizeTwoCyclicBaseResolvedRoute code y u x t) := by
      apply Finset.sum_congr rfl
      intro t _
      exact sizeTwoCyclicBaseResolvedRoute_card_symm code x t y u
    _ = _ :=
      sizeTwoCyclicBaseResolvedRoute_card_sum_targetDifferences code y x u

/-- At each fixed source base, the target-difference multiplicity matrix has
constant column sum `q - 2`.  Together with the local degree law, it is an
integer doubly-stochastic matrix. -/
theorem sizeTwoCyclicTargetDifferenceMultiplicity_base_column_sum
    {q : ℕ} [NeZero q] (hq1 : (1 : ZMod q) ≠ 0) {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (u : sizeTwoAllowedDifference q a) :
    (∑ t : sizeTwoAllowedDifference q a,
      sizeTwoCyclicTargetDifferenceMultiplicity code x t u) = q - 2 := by
  classical
  let AdmissibleBases := {y : ZMod q //
    u.1 ≠ x - y ∧ u.1 ≠ (x - y) - 1}
  let e : AdmissibleBases ≃ SizeTwoAdmissibleTargetRow q u.1 := {
    toFun := fun y => ⟨x - y.1, y.2⟩
    invFun := fun r => ⟨x - r.1, by simpa using r.2⟩
    left_inv := fun y => by apply Subtype.ext; simp
    right_inv := fun r => by apply Subtype.ext; simp }
  calc
    (∑ t : sizeTwoAllowedDifference q a,
      sizeTwoCyclicTargetDifferenceMultiplicity code x t u) =
        ∑ t : sizeTwoAllowedDifference q a, ∑ y : ZMod q,
          Fintype.card (SizeTwoCyclicBaseResolvedRoute code x t y u) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact (sizeTwoCyclicBaseResolvedRoute_card_sum code x t u).symm
    _ = ∑ y : ZMod q, ∑ t : sizeTwoAllowedDifference q a,
          Fintype.card (SizeTwoCyclicBaseResolvedRoute code x t y u) :=
      Finset.sum_comm
    _ = ∑ y : ZMod q,
        if u.1 ≠ x - y ∧ u.1 ≠ (x - y) - 1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      exact sizeTwoCyclicBaseResolvedRoute_card_sum_sourceDifferences
        code x y u
    _ = Fintype.card AdmissibleBases := by
      rw [Fintype.card_subtype, Finset.card_filter]
    _ = Fintype.card (SizeTwoAdmissibleTargetRow q u.1) :=
      Fintype.card_congr e
    _ = q - 2 := sizeTwoAdmissibleTargetRow_card q u.1 hq1

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicBaseResolvedRoute_card_le_one
#print axioms Erdos85.sizeTwoCyclicBaseResolvedRoute_card_symm
#print axioms Erdos85.sizeTwoCyclicBaseResolvedRoute_card_sum
#print axioms Erdos85.sizeTwoCyclicBaseResolvedRoute_card_column_sum
#print axioms
  Erdos85.sizeTwoCyclicBaseResolvedRoute_card_sum_targetDifferences
#print axioms
  Erdos85.sizeTwoCyclicBaseResolvedRoute_card_sum_sourceDifferences
#print axioms
  Erdos85.sizeTwoCyclicTargetDifferenceMultiplicity_base_column_sum
