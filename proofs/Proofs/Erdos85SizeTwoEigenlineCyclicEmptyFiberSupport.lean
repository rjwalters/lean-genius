import Proofs.Erdos85SizeTwoEigenlineCyclicSelectedFiberGraph
import Proofs.Erdos85SizeTwoEigenlineCyclicSelectedOrbitSupport
import Proofs.Erdos85SizeTwoEigenlineCyclicMatchingReplication
import Proofs.Erdos85SizeTwoEigenlineCyclicOrderedPairSecondMoment

/-!
# Collision pressure from an empty selected fiber

If the graph induced by one difference fiber has no edges, then matching
incidences sourced in that fiber cannot land back in the same fiber.  Their
support therefore loses an entire orbit of `q` cells.  This is the lower,
counting half of the three-cap middle-fiber nonemptiness mechanism.
-/

namespace Erdos85

noncomputable section

/-- Under an empty selected-fiber graph, a cell in the support of that
fiber's matching orbit has a different target fiber. -/
theorem sizeTwoCyclicMatchingOrbitSupport_targetDifference_ne_of_noAdj
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (hloop : code.toReciprocalCode.Loopless)
    (t : sizeTwoAllowedDifference q a)
    (hno : ∀ x y : ZMod q,
      ¬ (sizeTwoCyclicSelectedFiberGraph code.toReciprocalCode t).Adj x y)
    (e : {e // e ∈ sizeTwoCyclicSelectedOrbitSupport code {t}}) :
    (sizeTwoCyclicSelectedOrbitSupportSource code {t} e).2 ≠ t := by
  classical
  intro ht
  let target := sizeTwoCyclicSelectedOrbitSupportSource code {t} e
  change target.2 = t at ht
  have htarget : sizeTwoCyclicMatchingSourceCell target = e.1 :=
    sizeTwoCyclicSelectedOrbitSupportSource_spec code {t} e
  have hmult : sizeTwoCyclicMatchingOrbitMultiplicity code t e.1 ≠ 0 := by
    have he := (Finset.mem_filter.mp e.2).2
    simpa [sizeTwoCyclicSelectedOrbitMultiplicity] using he
  unfold sizeTwoCyclicMatchingOrbitMultiplicity at hmult
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hmult)
  have hmem := (Finset.mem_filter.mp hx).2
  let v : sizeTwoCyclicExteriorCell q a :=
    sizeTwoCyclicCellAt q a target.1 target.2
  have hv : v.1 = e.1 := by
    simpa [v, sizeTwoCyclicMatchingSourceCell, Prod.ext_iff] using htarget
  have hadjCode :
      (sizeTwoCyclicCodeGraph q a code.toReciprocalCode).Adj
        (sizeTwoCyclicCellAt q a x t) v :=
    (sizeTwoCyclicSourceMatching_mem_iff_graph_adj
      q a code hloop (x, t) v).mp (by simpa [hv] using hmem)
  have hadj :
      (sizeTwoCyclicSelectedFiberGraph code.toReciprocalCode t).Adj
        x target.1 := by
    rw [sizeTwoCyclicSelectedFiberGraph, SimpleGraph.comap_adj]
    convert hadjCode using 1
    simpa [v, ht]
  exact hno x target.1 hadj

/-- The support-source map, restricted by an empty selected fiber, lands in
the allowed cells outside that fiber. -/
def sizeTwoCyclicEmptyFiberSupportSource
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (hloop : code.toReciprocalCode.Loopless)
    (t : sizeTwoAllowedDifference q a)
    (hno : ∀ x y : ZMod q,
      ¬ (sizeTwoCyclicSelectedFiberGraph code.toReciprocalCode t).Adj x y) :
    {e // e ∈ sizeTwoCyclicSelectedOrbitSupport code {t}} →
      {source : SizeTwoCyclicMatchingSource q a // source.2 ≠ t} :=
  fun e => ⟨sizeTwoCyclicSelectedOrbitSupportSource code {t} e,
    sizeTwoCyclicMatchingOrbitSupport_targetDifference_ne_of_noAdj
      code hloop t hno e⟩

theorem sizeTwoCyclicEmptyFiberSupportSource_injective
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (hloop : code.toReciprocalCode.Loopless)
    (t : sizeTwoAllowedDifference q a)
    (hno : ∀ x y : ZMod q,
      ¬ (sizeTwoCyclicSelectedFiberGraph code.toReciprocalCode t).Adj x y) :
    Function.Injective
      (sizeTwoCyclicEmptyFiberSupportSource code hloop t hno) := by
  intro e f hef
  apply sizeTwoCyclicSelectedOrbitSupportSource_injective code {t}
  exact congrArg Subtype.val hef

/-- Removing the empty target fiber sharpens the support bound from
`q(q-2)` to `q(q-3)`. -/
theorem sizeTwoCyclicMatchingOrbitSupport_card_le_of_noAdj
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (hloop : code.toReciprocalCode.Loopless)
    (ha : a ≠ -1 - a)
    (t : sizeTwoAllowedDifference q a)
    (hno : ∀ x y : ZMod q,
      ¬ (sizeTwoCyclicSelectedFiberGraph code.toReciprocalCode t).Adj x y) :
    (sizeTwoCyclicSelectedOrbitSupport code {t}).card ≤ q * (q - 3) := by
  classical
  rw [← Fintype.card_coe]
  calc
    Fintype.card {e // e ∈ sizeTwoCyclicSelectedOrbitSupport code {t}} ≤
        Fintype.card {source : SizeTwoCyclicMatchingSource q a // source.2 ≠ t} :=
      Fintype.card_le_of_injective
        (sizeTwoCyclicEmptyFiberSupportSource code hloop t hno)
        (sizeTwoCyclicEmptyFiberSupportSource_injective code hloop t hno)
    _ = q * (q - 3) := by
      let sameFiberEquiv :
          {source : SizeTwoCyclicMatchingSource q a // source.2 = t} ≃
            ZMod q := {
        toFun := fun source => source.1.1
        invFun := fun x =>
          (⟨(x, t), rfl⟩ :
            {source : SizeTwoCyclicMatchingSource q a // source.2 = t})
        left_inv := fun (source :
            {source : SizeTwoCyclicMatchingSource q a // source.2 = t}) => by
          apply Subtype.ext
          apply Prod.ext
          · rfl
          · exact source.2.symm
        right_inv := fun x => rfl }
      have hsame : Fintype.card
          {source : SizeTwoCyclicMatchingSource q a // source.2 = t} = q := by
        rw [Fintype.card_congr sameFiberEquiv, ZMod.card]
      rw [Fintype.card_subtype_compl (fun source :
        SizeTwoCyclicMatchingSource q a => source.2 = t)]
      rw [sizeTwoCyclicMatchingSource_card q a ha]
      rw [hsame]
      rw [show q = q * 1 by omega, Nat.mul_sub_left_distrib]
      simp only [Nat.sub_sub]
      norm_num
      rw [Nat.mul_sub_left_distrib]
      omega

private theorem nat_le_one_add_choose_two (n : ℕ) :
    n ≤ 1 + n.choose 2 := by
  cases n with
  | zero => simp
  | succ n =>
      cases n with
      | zero => simp
      | succ k =>
          rw [Nat.choose_succ_succ, Nat.choose_one_right]
          omega

/-- If the selected fiber is empty, concentrating its exact incidence mass
on the remaining `q(q-3)` allowed cells forces collision load.  The
division-free statement is valid uniformly in `q`. -/
theorem sizeTwoCyclicMatchingOrbitMultiplicity_choose_two_emptyFiber_lower
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (hloop : code.toReciprocalCode.Loopless)
    (ha : a ≠ -1 - a) (hq1 : (1 : ZMod q) ≠ 0)
    (t : sizeTwoAllowedDifference q a)
    (hno : ∀ x y : ZMod q,
      ¬ (sizeTwoCyclicSelectedFiberGraph code.toReciprocalCode t).Adj x y) :
    q * (q - 2) ≤ q * (q - 3) +
      ∑ e : SizeTwoCyclicAbsoluteGridEdge q,
        (sizeTwoCyclicMatchingOrbitMultiplicity code t e).choose 2 := by
  classical
  let M := sizeTwoCyclicMatchingOrbitMultiplicity code t
  let S := sizeTwoCyclicSelectedOrbitSupport code {t}
  have hsupport (e : SizeTwoCyclicAbsoluteGridEdge q) :
      e ∈ S ↔ M e ≠ 0 := by
    simp [S, M, sizeTwoCyclicSelectedOrbitSupport,
      sizeTwoCyclicSelectedOrbitMultiplicity]
  have hsum : (∑ e ∈ S, M e) = q * (q - 2) := by
    calc
      (∑ e ∈ S, M e) = ∑ e : SizeTwoCyclicAbsoluteGridEdge q, M e := by
        apply Finset.sum_subset (Finset.subset_univ S)
        intro e heuniv heS
        have : M e = 0 := by
          by_contra hne
          exact heS ((hsupport e).mpr hne)
        simp [this]
      _ = q * (q - 2) := sizeTwoCyclicMatchingOrbitMultiplicity_sum
        code hq1 t
  calc
    q * (q - 2) = ∑ e ∈ S, M e := hsum.symm
    _ ≤ ∑ e ∈ S, (1 + (M e).choose 2) := by
      apply Finset.sum_le_sum
      intro e he
      exact nat_le_one_add_choose_two (M e)
    _ = S.card + ∑ e ∈ S, (M e).choose 2 := by
      simp_rw [Finset.sum_add_distrib]
      simp
    _ ≤ q * (q - 3) + ∑ e : SizeTwoCyclicAbsoluteGridEdge q,
          (M e).choose 2 := by
      apply Nat.add_le_add
      · exact sizeTwoCyclicMatchingOrbitSupport_card_le_of_noAdj
          code hloop ha t hno
      · exact Finset.sum_le_sum_of_subset (Finset.subset_univ S)
    _ = q * (q - 3) +
        ∑ e : SizeTwoCyclicAbsoluteGridEdge q,
          (sizeTwoCyclicMatchingOrbitMultiplicity code t e).choose 2 := rfl

/-- Once `q ≥ 3`, the division-free support inequality says directly that an
empty selected fiber forces at least `q` unordered repeated-target
incidences.  This is the q-generic collision-pressure entry point for any
subsequent binary valuation-layer transport argument. -/
theorem q_le_sizeTwoCyclicMatchingOrbitMultiplicity_choose_two_of_noAdj
    {q : ℕ} [NeZero q] {a : ZMod q}
    (hq : 3 ≤ q)
    (code : SizeTwoCyclicFullPermutationCode q a)
    (hloop : code.toReciprocalCode.Loopless)
    (ha : a ≠ -1 - a) (hq1 : (1 : ZMod q) ≠ 0)
    (t : sizeTwoAllowedDifference q a)
    (hno : ∀ x y : ZMod q,
      ¬ (sizeTwoCyclicSelectedFiberGraph code.toReciprocalCode t).Adj x y) :
    q ≤ ∑ e : SizeTwoCyclicAbsoluteGridEdge q,
      (sizeTwoCyclicMatchingOrbitMultiplicity code t e).choose 2 := by
  have h := sizeTwoCyclicMatchingOrbitMultiplicity_choose_two_emptyFiber_lower
    code hloop ha hq1 t hno
  have hsub : q - 2 = (q - 3) + 1 := by omega
  rw [hsub, Nat.mul_add] at h
  omega

/-- Base-resolved nonlinear form of the empty-fibre pressure: the total
same-fibre shifted-agreement mass over all bases and nonzero shifts is at
least `2q`.  Unlike a valuation-only aggregate, this is exactly the quantity
on which the code's positional agreement caps act. -/
theorem two_mul_q_le_sizeTwoCyclicAgreement_sum_of_noAdj
    {q : ℕ} [NeZero q] {a : ZMod q}
    (hq : 3 ≤ q)
    (code : SizeTwoCyclicFullPermutationCode q a)
    (hloop : code.toReciprocalCode.Loopless)
    (ha : a ≠ -1 - a) (hq1 : (1 : ZMod q) ≠ 0)
    (t : sizeTwoAllowedDifference q a)
    (hno : ∀ x y : ZMod q,
      ¬ (sizeTwoCyclicSelectedFiberGraph code.toReciprocalCode t).Adj x y) :
    2 * q ≤ ∑ xd : SizeTwoCyclicBaseNonzeroShift q,
      Fintype.card (SizeTwoCrossShiftedPermutationAgreement q a
        code.toReciprocalCode.toPermutationCode.perm
        xd.1 xd.2.1 t t) := by
  calc
    2 * q ≤ 2 * ∑ e : SizeTwoCyclicAbsoluteGridEdge q,
        (sizeTwoCyclicMatchingOrbitMultiplicity code t e).choose 2 :=
      Nat.mul_le_mul_left 2
        (q_le_sizeTwoCyclicMatchingOrbitMultiplicity_choose_two_of_noAdj
          hq code hloop ha hq1 t hno)
    _ = _ :=
      two_mul_sizeTwoCyclicMatchingOrbitMultiplicity_choose_two_sum_eq_agreement_shifts
        code t

/-- At the calibrated `q=8` parameter, an empty selected fiber forces at
least eight unordered repeated-target incidences in that fiber. -/
theorem eight_le_sizeTwoCyclicMatchingOrbitMultiplicity_choose_two_of_noAdj
    {a : ZMod 8}
    (code : SizeTwoCyclicFullPermutationCode 8 a)
    (hloop : code.toReciprocalCode.Loopless)
    (ha : a ≠ -1 - a)
    (t : sizeTwoAllowedDifference 8 a)
    (hno : ∀ x y : ZMod 8,
      ¬ (sizeTwoCyclicSelectedFiberGraph code.toReciprocalCode t).Adj x y) :
    8 ≤ ∑ e : SizeTwoCyclicAbsoluteGridEdge 8,
      (sizeTwoCyclicMatchingOrbitMultiplicity code t e).choose 2 := by
  exact q_le_sizeTwoCyclicMatchingOrbitMultiplicity_choose_two_of_noAdj
    (by norm_num) code hloop ha (by decide) t hno

end

end Erdos85

#print axioms
  Erdos85.sizeTwoCyclicMatchingOrbitSupport_targetDifference_ne_of_noAdj
#print axioms Erdos85.sizeTwoCyclicMatchingOrbitSupport_card_le_of_noAdj
#print axioms
  Erdos85.sizeTwoCyclicMatchingOrbitMultiplicity_choose_two_emptyFiber_lower
#print axioms
  Erdos85.q_le_sizeTwoCyclicMatchingOrbitMultiplicity_choose_two_of_noAdj
#print axioms Erdos85.two_mul_q_le_sizeTwoCyclicAgreement_sum_of_noAdj
#print axioms
  Erdos85.eight_le_sizeTwoCyclicMatchingOrbitMultiplicity_choose_two_of_noAdj
