import Proofs.Erdos85QuotientCutParity
import Proofs.Erdos85MixedAnchorQuantization
import Proofs.Erdos85MixedAnchorFiber

/-!
# Parity cancellation for equal-length off-diagonal blocks

Transpose symmetry identifies the ordered-difference sets of the two
orientations of an equal-length component pair.  Hence every fiber count
from an ordered pair `(c,e)` is repeated by `(e,c)`, and the total over
distinct pairs is even.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- A symmetric weight has even total over the ordered off-diagonal of a
finite set. -/
theorem even_sum_erase_of_symmetric
    {C : Type*} [DecidableEq C] (S : Finset C) (F : C → C → ℕ)
    (hsymm : ∀ c ∈ S, ∀ e ∈ S, F c e = F e c) :
    Even (∑ c ∈ S, ∑ e ∈ S.erase c, F c e) := by
  let Q : C → C → ℕ := fun c e ↦ if c = e then 0 else F c e
  have hprincipal : Even (∑ c ∈ S, ∑ e ∈ S, Q c e) := by
    apply even_principal_sum_of_pair_even S Q
    · intro c hc
      simp [Q]
    · intro c hc e he hce
      rw [Nat.even_add]
      simp only [Q, hce, if_false, hce.symm, hsymm c hc e he]
  have heq : (∑ c ∈ S, ∑ e ∈ S, Q c e) =
      ∑ c ∈ S, ∑ e ∈ S.erase c, F c e := by
    apply Finset.sum_congr rfl
    intro c hc
    calc
      ∑ e ∈ S, Q c e = (∑ e ∈ S.erase c, Q c e) + Q c c :=
        (Finset.sum_erase_add _ _ hc).symm
      _ = ∑ e ∈ S.erase c, F c e := by
        simp only [Q, if_pos]
        apply Finset.sum_congr rfl
        intro e he
        have hne : c ≠ e := (Finset.mem_erase.mp he).1.symm
        simp [hne]
  rw [heq] at hprincipal
  exact hprincipal

/-- **Equal-block fiber cancellation.** For a common family of equally
parametrized odd defect cycles, the number of admissible displacements in a
fixed projection fiber whose full pair mass is supplied by another cycle of
the family is even after summing over ordered distinct cycle pairs. -/
theorem even_sum_equalBlock_fullMass_fiber
    {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d n p : ℕ} [NeZero n] [NeZero p]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hn3 : 3 ≤ n) (hnOdd : Odd n) (hpn : p ∣ n)
    (u : C → ZMod n → V)
    (hu : ∀ c, Function.Injective (u c))
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (S : Finset C) (t : ZMod p) :
    Even (∑ e ∈ S, ∑ c ∈ S.erase e,
      ((admissibleDifferences n).filter (fun δ ↦
        ZMod.castHom hpn (ZMod p) δ = t ∧
          (∑ x : ZMod n,
            anchorPairMultiplicity G (u c x) (u e) δ) = n)).card) := by
  let D := secondOrderDefectGraph G
  let F : C → C → ℕ := fun c e ↦
    ((admissibleDifferences n).filter (fun δ ↦
      ZMod.castHom hpn (ZMod p) δ = t ∧
        (∑ x : ZMod n,
          anchorPairMultiplicity G (u c x) (u e) δ) = n)).card
  have hcomm := adjMatrix_comm_secondOrderDefect_of_even
    G hfree hd heven hmin hcard
  have hF (c e : C) : F c e =
      ((orderedDifferenceSet (mixedAnchorSupport G (u c 0) (u e))).filter
        (fun δ ↦ ZMod.castHom hpn (ZMod p) δ = t)).card := by
    apply congrArg Finset.card
    ext δ
    rw [Finset.mem_filter, Finset.mem_filter]
    have hδadm := mem_admissibleDifferences_iff δ
    constructor
    · rintro ⟨hδa, hcast, hmass⟩
      have hδ0 : δ ≠ 0 := hδadm.mp hδa |>.1
      have hm := sum_anchorPairMultiplicity_of_equalSize G D hn3 hnOdd
        (u c) (u e) (hu c) (hu e) hcomm (huD c) (huD e) hfree δ hδ0
      split_ifs at hm with hmem
      · exact ⟨hmem, hcast⟩
      · omega
    · rintro ⟨hmem, hcast⟩
      have hδ0 : δ ≠ 0 := by
        intro h
        subst δ
        exact zero_not_mem_orderedDifferenceSet _ hmem
      have hδa : δ ∈ admissibleDifferences n := by
        rw [mem_admissibleDifferences_iff]
        have hone : (1 : ZMod n) ≠ 0 := by
          intro h
          have := ZMod.one_eq_zero_iff.mp h
          omega
        refine ⟨hδ0, ?_, ?_⟩
        · intro h1
          rw [h1, mem_orderedDifferenceSet_iff_exists_pair _ _ hone] at hmem
          obtain ⟨b, hb, hb1⟩ := hmem
          exact mixedAnchorSupport_no_consecutive G hfree hd heven hmin hcard
            (hu e) hn3 (huD e) (u c 0) b hb hb1
        · intro hm1
          have hmone : (-1 : ZMod n) ≠ 0 := neg_ne_zero.mpr hone
          rw [hm1, mem_orderedDifferenceSet_iff_exists_pair _ _ hmone] at hmem
          obtain ⟨b, hb, hbm⟩ := hmem
          have hbm' : b - 1 ∈ mixedAnchorSupport G (u c 0) (u e) := by
            simpa [sub_eq_add_neg] using hbm
          have hb' : (b - 1) + 1 ∈ mixedAnchorSupport G (u c 0) (u e) := by
            simpa using hb
          exact mixedAnchorSupport_no_consecutive G hfree hd heven hmin hcard
            (hu e) hn3 (huD e) (u c 0) (b - 1) hbm' hb'
      have hm := sum_anchorPairMultiplicity_of_equalSize G D hn3 hnOdd
        (u c) (u e) (hu c) (hu e) hcomm (huD c) (huD e) hfree δ hδ0
      rw [if_pos hmem] at hm
      exact ⟨hδa, hcast, hm⟩
  let F' : C → C → ℕ := fun e c ↦ F c e
  change Even (∑ e ∈ S, ∑ c ∈ S.erase e, F' e c)
  apply even_sum_erase_of_symmetric S F'
  intro c hc e he
  change F e c = F c e
  rw [hF e c, hF c e]
  apply congrArg Finset.card
  have hs := orderedDifferenceSet_graphCycleBlockZeroSupport_symm hn3 hnOdd
    G D (u c) (u e) (hu c) (hu e) hcomm (huD c) (huD e)
  rw [mixedAnchorSupport_eq_graphCycleBlockZeroSupport,
    mixedAnchorSupport_eq_graphCycleBlockZeroSupport, hs]

end

end Erdos85
