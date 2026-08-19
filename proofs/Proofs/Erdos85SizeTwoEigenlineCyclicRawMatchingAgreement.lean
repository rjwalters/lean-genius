import Proofs.Erdos85SizeTwoEigenlineCyclicMatchingSecondMomentCensus
import Proofs.Erdos85SizeTwoEigenlineCyclicOrderedPairSecondMoment
import Proofs.Erdos85SizeTwoEigenlineCyclicTwoFiberSubsystem

/-!
# Matching/agreement equivalence for a raw cyclic permutation family

The earlier matching API is packaged around a full code.  The packing
conjecture retains only same-difference agreement, so this file exposes the
underlying equivalence at the permutation-family level, with no cross-fiber
agreement assumptions.
-/

namespace Erdos85

noncomputable section

def sizeTwoCyclicRawMatchingEdge
    {q : ℕ} [NeZero q] {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (source : SizeTwoCyclicMatchingSource q a)
    (r : SizeTwoAdmissibleTargetRow q source.2.1) :
    SizeTwoCyclicAbsoluteGridEdge q :=
  (source.1 + r.1, source.1 + (P source.1 source.2 r).1)

theorem sizeTwoCyclicRawMatchingEdge_injective
    {q : ℕ} [NeZero q] {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (source : SizeTwoCyclicMatchingSource q a) :
    Function.Injective (sizeTwoCyclicRawMatchingEdge P source) := by
  intro r s hrs
  apply Subtype.ext
  exact add_left_cancel (congrArg Prod.fst hrs)

def sizeTwoCyclicRawSourceMatching
    {q : ℕ} [NeZero q] {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (source : SizeTwoCyclicMatchingSource q a) :
    Finset (SizeTwoCyclicAbsoluteGridEdge q) :=
  Finset.univ.image (sizeTwoCyclicRawMatchingEdge P source)

theorem sizeTwoCyclicRawSourceMatching_mem_iff
    {q : ℕ} [NeZero q] {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (source : SizeTwoCyclicMatchingSource q a)
    (e : SizeTwoCyclicAbsoluteGridEdge q) :
    e ∈ sizeTwoCyclicRawSourceMatching P source ↔
      ∃ r, sizeTwoCyclicRawMatchingEdge P source r = e := by
  classical
  simp [sizeTwoCyclicRawSourceMatching]

def sizeTwoCyclicRawIntersectionFirstRow
    {q : ℕ} [NeZero q] {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (source₁ source₂ : SizeTwoCyclicMatchingSource q a)
    (e : {e : SizeTwoCyclicAbsoluteGridEdge q //
      e ∈ sizeTwoCyclicRawSourceMatching P source₁ ∩
        sizeTwoCyclicRawSourceMatching P source₂}) :
    SizeTwoAdmissibleTargetRow q source₁.2.1 :=
  Classical.choose ((sizeTwoCyclicRawSourceMatching_mem_iff P source₁ e.1).mp
    (Finset.mem_inter.mp e.2).1)

theorem sizeTwoCyclicRawIntersectionFirstRow_spec
    {q : ℕ} [NeZero q] {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (source₁ source₂ : SizeTwoCyclicMatchingSource q a)
    (e : {e : SizeTwoCyclicAbsoluteGridEdge q //
      e ∈ sizeTwoCyclicRawSourceMatching P source₁ ∩
        sizeTwoCyclicRawSourceMatching P source₂}) :
    sizeTwoCyclicRawMatchingEdge P source₁
      (sizeTwoCyclicRawIntersectionFirstRow P source₁ source₂ e) = e.1 :=
  Classical.choose_spec
    ((sizeTwoCyclicRawSourceMatching_mem_iff P source₁ e.1).mp
      (Finset.mem_inter.mp e.2).1)

def sizeTwoCyclicRawIntersectionSecondRow
    {q : ℕ} [NeZero q] {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (source₁ source₂ : SizeTwoCyclicMatchingSource q a)
    (e : {e : SizeTwoCyclicAbsoluteGridEdge q //
      e ∈ sizeTwoCyclicRawSourceMatching P source₁ ∩
        sizeTwoCyclicRawSourceMatching P source₂}) :
    SizeTwoAdmissibleTargetRow q source₂.2.1 :=
  Classical.choose ((sizeTwoCyclicRawSourceMatching_mem_iff P source₂ e.1).mp
    (Finset.mem_inter.mp e.2).2)

theorem sizeTwoCyclicRawIntersectionSecondRow_spec
    {q : ℕ} [NeZero q] {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (source₁ source₂ : SizeTwoCyclicMatchingSource q a)
    (e : {e : SizeTwoCyclicAbsoluteGridEdge q //
      e ∈ sizeTwoCyclicRawSourceMatching P source₁ ∩
        sizeTwoCyclicRawSourceMatching P source₂}) :
    sizeTwoCyclicRawMatchingEdge P source₂
      (sizeTwoCyclicRawIntersectionSecondRow P source₁ source₂ e) = e.1 :=
  Classical.choose_spec
    ((sizeTwoCyclicRawSourceMatching_mem_iff P source₂ e.1).mp
      (Finset.mem_inter.mp e.2).2)

def sizeTwoCyclicRawIntersectionAgreement
    {q : ℕ} [NeZero q] {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (source₁ source₂ : SizeTwoCyclicMatchingSource q a)
    (e : {e : SizeTwoCyclicAbsoluteGridEdge q //
      e ∈ sizeTwoCyclicRawSourceMatching P source₁ ∩
        sizeTwoCyclicRawSourceMatching P source₂}) :
    SizeTwoCrossShiftedPermutationAgreement q a P
      source₁.1 (source₂.1 - source₁.1) source₁.2 source₂.2 := by
  let r₁ := sizeTwoCyclicRawIntersectionFirstRow P source₁ source₂ e
  let r₂ := sizeTwoCyclicRawIntersectionSecondRow P source₁ source₂ e
  have hr₁ := sizeTwoCyclicRawIntersectionFirstRow_spec P source₁ source₂ e
  have hr₂ := sizeTwoCyclicRawIntersectionSecondRow_spec P source₁ source₂ e
  have hedge : sizeTwoCyclicRawMatchingEdge P source₁ r₁ =
      sizeTwoCyclicRawMatchingEdge P source₂ r₂ := hr₁.trans hr₂.symm
  have hrow : r₂.1 = r₁.1 - (source₂.1 - source₁.1) := by
    have h := congrArg Prod.fst hedge
    dsimp [sizeTwoCyclicRawMatchingEdge] at h
    calc
      r₂.1 = -source₂.1 + (source₂.1 + r₂.1) := by abel
      _ = -source₂.1 + (source₁.1 + r₁.1) := by rw [← h]
      _ = r₁.1 - (source₂.1 - source₁.1) := by abel
  refine ⟨r₁, by simpa [← hrow] using r₂.2, ?_⟩
  have h := congrArg Prod.snd hedge
  have hr₂eq : r₂ =
      ⟨r₁.1 - (source₂.1 - source₁.1), by
        simpa [← hrow] using r₂.2⟩ := Subtype.ext hrow
  rw [← hr₂eq]
  simpa [sizeTwoCyclicRawMatchingEdge, add_assoc] using h

theorem sizeTwoCyclicRawIntersectionAgreement_injective
    {q : ℕ} [NeZero q] {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (source₁ source₂ : SizeTwoCyclicMatchingSource q a) :
    Function.Injective (sizeTwoCyclicRawIntersectionAgreement P source₁ source₂) := by
  intro e f hef
  apply Subtype.ext
  rw [← sizeTwoCyclicRawIntersectionFirstRow_spec P source₁ source₂ e,
    ← sizeTwoCyclicRawIntersectionFirstRow_spec P source₁ source₂ f]
  apply congrArg (sizeTwoCyclicRawMatchingEdge P source₁)
  simpa [sizeTwoCyclicRawIntersectionAgreement] using
    congrArg (fun w => w.row) hef

def sizeTwoCyclicRawAgreementIntersectionEdge
    {q : ℕ} [NeZero q] {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (source₁ source₂ : SizeTwoCyclicMatchingSource q a)
    (w : SizeTwoCrossShiftedPermutationAgreement q a P
      source₁.1 (source₂.1 - source₁.1) source₁.2 source₂.2) :
    {e : SizeTwoCyclicAbsoluteGridEdge q //
      e ∈ sizeTwoCyclicRawSourceMatching P source₁ ∩
        sizeTwoCyclicRawSourceMatching P source₂} := by
  let r₂ : SizeTwoAdmissibleTargetRow q source₂.2.1 :=
    ⟨w.row.1 - (source₂.1 - source₁.1), w.shifted_admissible⟩
  refine ⟨sizeTwoCyclicRawMatchingEdge P source₁ w.row, ?_⟩
  apply Finset.mem_inter.mpr
  constructor
  · exact (sizeTwoCyclicRawSourceMatching_mem_iff P source₁ _).mpr ⟨w.row, rfl⟩
  · apply (sizeTwoCyclicRawSourceMatching_mem_iff P source₂ _).mpr
    refine ⟨r₂, ?_⟩
    apply Prod.ext
    · dsimp [sizeTwoCyclicRawMatchingEdge, r₂]
      abel
    · dsimp [sizeTwoCyclicRawMatchingEdge, r₂]
      simpa [add_assoc] using w.column_eq.symm

theorem sizeTwoCyclicRawIntersectionAgreement_surjective
    {q : ℕ} [NeZero q] {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (source₁ source₂ : SizeTwoCyclicMatchingSource q a) :
    Function.Surjective (sizeTwoCyclicRawIntersectionAgreement P source₁ source₂) := by
  intro w
  let e := sizeTwoCyclicRawAgreementIntersectionEdge P source₁ source₂ w
  refine ⟨e, ?_⟩
  apply SizeTwoCrossShiftedPermutationAgreement.row_injective
  apply sizeTwoCyclicRawMatchingEdge_injective P source₁
  change sizeTwoCyclicRawMatchingEdge P source₁
      (sizeTwoCyclicRawIntersectionFirstRow P source₁ source₂ e) =
    sizeTwoCyclicRawMatchingEdge P source₁ w.row
  rw [sizeTwoCyclicRawIntersectionFirstRow_spec P source₁ source₂ e]
  rfl

/-- Raw-code bridge: a matching intersection has exactly as many elements as
the corresponding shifted-agreement type. -/
theorem sizeTwoCyclicRawSourceMatching_inter_card_eq_agreement
    {q : ℕ} [NeZero q] {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (source₁ source₂ : SizeTwoCyclicMatchingSource q a) :
    (sizeTwoCyclicRawSourceMatching P source₁ ∩
      sizeTwoCyclicRawSourceMatching P source₂).card =
      Fintype.card (SizeTwoCrossShiftedPermutationAgreement q a P
        source₁.1 (source₂.1 - source₁.1) source₁.2 source₂.2) := by
  rw [← Fintype.card_coe]
  exact Fintype.card_congr (Equiv.ofBijective
    (sizeTwoCyclicRawIntersectionAgreement P source₁ source₂)
    ⟨sizeTwoCyclicRawIntersectionAgreement_injective P source₁ source₂,
      sizeTwoCyclicRawIntersectionAgreement_surjective P source₁ source₂⟩)

def sizeTwoCyclicRawMatchingOrbitMultiplicity
    {q : ℕ} [NeZero q] {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (t : sizeTwoAllowedDifference q a)
    (e : SizeTwoCyclicAbsoluteGridEdge q) : ℕ :=
  ((Finset.univ : Finset (ZMod q)).filter fun x =>
    e ∈ sizeTwoCyclicRawSourceMatching P (x, t)).card

/-- Exact incidence-transpose census for one raw difference fiber. -/
theorem sizeTwoCyclicRawMatchingOrbitMultiplicity_choose_two_sum
    {q : ℕ} [NeZero q] {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (t : sizeTwoAllowedDifference q a) :
    (∑ e : SizeTwoCyclicAbsoluteGridEdge q,
      (sizeTwoCyclicRawMatchingOrbitMultiplicity P t e).choose 2) =
      ∑ pair ∈ (Finset.univ : Finset (ZMod q)).powersetCard 2,
        ((Finset.univ : Finset (SizeTwoCyclicAbsoluteGridEdge q)).filter
          fun e => pair ⊆
            ((Finset.univ : Finset (ZMod q)).filter fun x =>
              e ∈ sizeTwoCyclicRawSourceMatching P (x, t))).card := by
  let Inc : ZMod q → SizeTwoCyclicAbsoluteGridEdge q → Prop :=
    fun x e => e ∈ sizeTwoCyclicRawSourceMatching P (x, t)
  simpa [Inc, Erdos101OQ02ST.pointsOn,
    sizeTwoCyclicRawMatchingOrbitMultiplicity] using
    (sum_choose_two_pointsOn_eq_sum_commonTargets Inc
      (Finset.univ : Finset (ZMod q))
      (Finset.univ : Finset (SizeTwoCyclicAbsoluteGridEdge q)))

theorem two_mul_sizeTwoCyclicRawMatchingOrbitMultiplicity_choose_two_sum
    {q : ℕ} [NeZero q] {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (t : sizeTwoAllowedDifference q a) :
    2 * (∑ e : SizeTwoCyclicAbsoluteGridEdge q,
      (sizeTwoCyclicRawMatchingOrbitMultiplicity P t e).choose 2) =
      ∑ p ∈ (Finset.univ : Finset (ZMod q)).offDiag,
        (sizeTwoCyclicRawSourceMatching P (p.1, t) ∩
          sizeTwoCyclicRawSourceMatching P (p.2, t)).card := by
  let Inc : ZMod q → SizeTwoCyclicAbsoluteGridEdge q → Prop :=
    fun x e => e ∈ sizeTwoCyclicRawSourceMatching P (x, t)
  calc
    _ = ∑ p ∈ (Finset.univ : Finset (ZMod q)).offDiag,
        ((Finset.univ : Finset (SizeTwoCyclicAbsoluteGridEdge q)).filter
          fun e => e ∈ sizeTwoCyclicRawSourceMatching P (p.1, t) ∧
            e ∈ sizeTwoCyclicRawSourceMatching P (p.2, t)).card := by
      simpa [Inc, Erdos101OQ02ST.pointsOn,
        sizeTwoCyclicRawMatchingOrbitMultiplicity] using
        (two_mul_sum_choose_two_pointsOn_eq_sum_offDiag_commonTargets Inc
          (Finset.univ : Finset (ZMod q))
          (Finset.univ : Finset (SizeTwoCyclicAbsoluteGridEdge q)))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      congr 1
      ext e
      simp

/-- Exact raw autocorrelation identity: the ordered shifted-agreement mass
is twice the target-multiplicity collision mass. -/
theorem two_mul_sizeTwoCyclicRawMatchingOrbitMultiplicity_choose_two_sum_eq_agreement
    {q : ℕ} [NeZero q] {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (t : sizeTwoAllowedDifference q a) :
    2 * (∑ e : SizeTwoCyclicAbsoluteGridEdge q,
      (sizeTwoCyclicRawMatchingOrbitMultiplicity P t e).choose 2) =
      ∑ xd : SizeTwoCyclicBaseNonzeroShift q,
        Fintype.card (SizeTwoCrossShiftedPermutationAgreement
          q a P xd.1 xd.2.1 t t) := by
  calc
    _ = ∑ p ∈ (Finset.univ : Finset (ZMod q)).offDiag,
        (sizeTwoCyclicRawSourceMatching P (p.1, t) ∩
          sizeTwoCyclicRawSourceMatching P (p.2, t)).card :=
      two_mul_sizeTwoCyclicRawMatchingOrbitMultiplicity_choose_two_sum P t
    _ = ∑ p ∈ (Finset.univ : Finset (ZMod q)).offDiag,
        Fintype.card (SizeTwoCrossShiftedPermutationAgreement
          q a P p.1 (p.2 - p.1) t t) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact sizeTwoCyclicRawSourceMatching_inter_card_eq_agreement
        P (p.1, t) (p.2, t)
    _ = ∑ p : SizeTwoCyclicDistinctBasePair q,
        Fintype.card (SizeTwoCrossShiftedPermutationAgreement
          q a P p.1.1 (p.1.2 - p.1.1) t t) := by
      rw [Finset.sum_subtype
        ((Finset.univ : Finset (ZMod q)).offDiag)
        (p := fun p : ZMod q × ZMod q => p.1 ≠ p.2)
        (fun p => by simp [Finset.mem_offDiag])]
    _ = _ := sizeTwoCyclicAgreement_sum_distinctPairs_eq_sum_shifts P t

/-- A reduced same-difference agreement law is exactly an upper bound on the
raw one-fiber matching collision moment. -/
theorem two_mul_sizeTwoCyclicRawMatchingOrbitMultiplicity_choose_two_sum_le
    {q : ℕ} [NeZero q] {a : ZMod q}
    (data : SizeTwoCyclicRoutingData q a)
    (t : sizeTwoAllowedDifference q a)
    (hagreement : data.AgreementAt t) :
    2 * (∑ e : SizeTwoCyclicAbsoluteGridEdge q,
      (sizeTwoCyclicRawMatchingOrbitMultiplicity data.perm t e).choose 2) ≤
      q * (q - 1) := by
  rw [two_mul_sizeTwoCyclicRawMatchingOrbitMultiplicity_choose_two_sum_eq_agreement]
  calc
    _ ≤ ∑ _xd : SizeTwoCyclicBaseNonzeroShift q, 1 := by
      apply Finset.sum_le_sum
      intro xd hxd
      exact hagreement xd.1 xd.2.1 xd.2.2
    _ = q * (q - 1) := by
      simp [Fintype.card_congr (Equiv.Set.univ _)]

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicRawSourceMatching_inter_card_eq_agreement
#print axioms Erdos85.sizeTwoCyclicRawMatchingOrbitMultiplicity_choose_two_sum
#print axioms Erdos85.two_mul_sizeTwoCyclicRawMatchingOrbitMultiplicity_choose_two_sum_eq_agreement
#print axioms Erdos85.two_mul_sizeTwoCyclicRawMatchingOrbitMultiplicity_choose_two_sum_le
