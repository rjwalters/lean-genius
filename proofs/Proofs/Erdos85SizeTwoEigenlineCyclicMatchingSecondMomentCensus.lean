import Proofs.Erdos85SizeTwoEigenlineCyclicMatchingAgreementEquiv
import Proofs.Erdos101ProblemOQ02

/-!
# Exact second-moment census for cyclic source matchings

This file records the incidence-transpose identity behind the orbit second
moment.  Counting a target point together with an unordered pair of incident
sources is the same as counting a source pair together with a common target.
For one cyclic difference orbit this identifies target multiplicity cherries
with pairwise matching intersections exactly.
-/

namespace Erdos85

noncomputable section

/-- General incidence transpose for unordered pairs. -/
theorem sum_choose_two_pointsOn_eq_sum_commonTargets
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (Inc : α → β → Prop) [DecidableRel Inc]
    (P : Finset α) (L : Finset β) :
    (∑ l ∈ L, (Erdos101OQ02ST.pointsOn Inc P l).card.choose 2) =
      ∑ e ∈ P.powersetCard 2,
        (L.filter fun l => e ⊆ Erdos101OQ02ST.pointsOn Inc P l).card := by
  classical
  calc
    (∑ l ∈ L, (Erdos101OQ02ST.pointsOn Inc P l).card.choose 2) =
        ∑ l ∈ L, ∑ e ∈ P.powersetCard 2,
          if e ⊆ Erdos101OQ02ST.pointsOn Inc P l then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [show (Erdos101OQ02ST.pointsOn Inc P l).card.choose 2 =
          ((Erdos101OQ02ST.pointsOn Inc P l).powersetCard 2).card from
        (Finset.card_powersetCard 2
          (Erdos101OQ02ST.pointsOn Inc P l)).symm]
      rw [show (Erdos101OQ02ST.pointsOn Inc P l).powersetCard 2 =
          (P.powersetCard 2).filter
        (fun e => e ⊆ Erdos101OQ02ST.pointsOn Inc P l) by
        ext e
        simp only [Finset.mem_powersetCard, Finset.mem_filter]
        constructor
        · intro h
          exact ⟨⟨h.1.trans
            (Erdos101OQ02ST.pointsOn_subset Inc P l), h.2⟩, h.1⟩
        · intro h
          exact ⟨h.2, h.1.2⟩]
      rw [Finset.card_filter]
    _ = ∑ e ∈ P.powersetCard 2, ∑ l ∈ L,
          if e ⊆ Erdos101OQ02ST.pointsOn Inc P l then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ e ∈ P.powersetCard 2,
        (L.filter fun l => e ⊆ Erdos101OQ02ST.pointsOn Inc P l).card := by
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.card_filter]

/-- Multiplicity of an absolute grid edge among the source matchings in one
fixed cyclic difference orbit. -/
def sizeTwoCyclicMatchingOrbitMultiplicity
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (t : sizeTwoAllowedDifference q a)
    (e : SizeTwoCyclicAbsoluteGridEdge q) : ℕ :=
  ((Finset.univ : Finset (ZMod q)).filter fun x =>
    e ∈ sizeTwoCyclicSourceMatching code (x, t)).card

/-- Exact second-moment census for one difference orbit. -/
theorem sizeTwoCyclicMatchingOrbitMultiplicity_choose_two_sum
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (t : sizeTwoAllowedDifference q a) :
    (∑ e : SizeTwoCyclicAbsoluteGridEdge q,
        (sizeTwoCyclicMatchingOrbitMultiplicity code t e).choose 2) =
      ∑ pair ∈ (Finset.univ : Finset (ZMod q)).powersetCard 2,
        ((Finset.univ : Finset (SizeTwoCyclicAbsoluteGridEdge q)).filter
          fun e => pair ⊆
            ((Finset.univ : Finset (ZMod q)).filter fun x =>
              e ∈ sizeTwoCyclicSourceMatching code (x, t))).card := by
  classical
  let Inc : ZMod q → SizeTwoCyclicAbsoluteGridEdge q → Prop :=
    fun x e => e ∈ sizeTwoCyclicSourceMatching code (x, t)
  simpa [Inc, Erdos101OQ02ST.pointsOn,
    sizeTwoCyclicMatchingOrbitMultiplicity] using
    (sum_choose_two_pointsOn_eq_sum_commonTargets Inc
      (Finset.univ : Finset (ZMod q))
      (Finset.univ : Finset (SizeTwoCyclicAbsoluteGridEdge q)))

/-- For an explicit source pair, the common-target filter is its matching
intersection. -/
theorem sizeTwoCyclicMatchingPair_commonTargets_card
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (t : sizeTwoAllowedDifference q a) (x y : ZMod q) :
    ((Finset.univ : Finset (SizeTwoCyclicAbsoluteGridEdge q)).filter
      fun e => ({x, y} : Finset (ZMod q)) ⊆
        ((Finset.univ : Finset (ZMod q)).filter fun z =>
          e ∈ sizeTwoCyclicSourceMatching code (z, t))).card =
      (sizeTwoCyclicSourceMatching code (x, t) ∩
        sizeTwoCyclicSourceMatching code (y, t)).card := by
  classical
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_inter]
  constructor
  · intro h
    have hx : x ∈ ({x, y} : Finset (ZMod q)) := by simp
    have hy : y ∈ ({x, y} : Finset (ZMod q)) := by simp
    exact ⟨(Finset.mem_filter.mp (h hx)).2,
      (Finset.mem_filter.mp (h hy)).2⟩
  · intro h z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.2⟩

/-- An explicit pair's contribution to the second-moment census is exactly
its shifted-agreement cardinality. -/
theorem sizeTwoCyclicMatchingPair_commonTargets_card_eq_agreement
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (t : sizeTwoAllowedDifference q a) (x y : ZMod q) :
    ((Finset.univ : Finset (SizeTwoCyclicAbsoluteGridEdge q)).filter
      fun e => ({x, y} : Finset (ZMod q)) ⊆
        ((Finset.univ : Finset (ZMod q)).filter fun z =>
          e ∈ sizeTwoCyclicSourceMatching code (z, t))).card =
      Fintype.card (SizeTwoCrossShiftedPermutationAgreement q a
        code.toReciprocalCode.toPermutationCode.perm
        x (y - x) t t) := by
  rw [sizeTwoCyclicMatchingPair_commonTargets_card code t x y]
  exact sizeTwoCyclicSourceMatching_inter_card_eq_agreement
    code (x, t) (y, t)

/-- Pairs of bases in one source-difference fibre that saturate the
codegree-one matching-intersection cap. -/
def sizeTwoCyclicSaturatedMatchingPairs
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (t : sizeTwoAllowedDifference q a) : Finset (Finset (ZMod q)) :=
  ((Finset.univ : Finset (ZMod q)).powersetCard 2).filter fun pair =>
    ((Finset.univ : Finset (SizeTwoCyclicAbsoluteGridEdge q)).filter
      fun e => pair ⊆
        ((Finset.univ : Finset (ZMod q)).filter fun x =>
          e ∈ sizeTwoCyclicSourceMatching code (x, t))).card = 1

/-- Within one source fibre, collision mass counts saturated source pairs
exactly.  Thus the quadratic cap obstruction can be treated as a finite set
of blockers rather than only as a second-moment sum. -/
theorem sizeTwoCyclicMatchingOrbitMultiplicity_choose_two_sum_eq_saturated
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (t : sizeTwoAllowedDifference q a) :
    (∑ e : SizeTwoCyclicAbsoluteGridEdge q,
        (sizeTwoCyclicMatchingOrbitMultiplicity code t e).choose 2) =
      (sizeTwoCyclicSaturatedMatchingPairs code t).card := by
  classical
  rw [sizeTwoCyclicMatchingOrbitMultiplicity_choose_two_sum]
  unfold sizeTwoCyclicSaturatedMatchingPairs
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro pair hpair
  have hcard : pair.card = 2 := (Finset.mem_powersetCard.mp hpair).2
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
  let common :=
    ((Finset.univ : Finset (SizeTwoCyclicAbsoluteGridEdge q)).filter
      fun e => ({x, y} : Finset (ZMod q)) ⊆
        ((Finset.univ : Finset (ZMod q)).filter fun z =>
          e ∈ sizeTwoCyclicSourceMatching code (z, t))).card
  have hcommon : common ≤ 1 := by
    rw [show common =
        (sizeTwoCyclicSourceMatching code (x, t) ∩
          sizeTwoCyclicSourceMatching code (y, t)).card by
      exact sizeTwoCyclicMatchingPair_commonTargets_card code t x y]
    apply sizeTwoCyclicSourceMatching_inter_card_le_one
    intro h
    apply hxy
    exact congrArg Prod.fst h
  change common = if common = 1 then 1 else 0
  by_cases hone : common = 1
  · simp [hone]
  · rw [if_neg hone]
    omega

end

end Erdos85

#print axioms Erdos85.sum_choose_two_pointsOn_eq_sum_commonTargets
#print axioms Erdos85.sizeTwoCyclicMatchingOrbitMultiplicity_choose_two_sum
#print axioms Erdos85.sizeTwoCyclicMatchingPair_commonTargets_card_eq_agreement
#print axioms
  Erdos85.sizeTwoCyclicMatchingOrbitMultiplicity_choose_two_sum_eq_saturated
