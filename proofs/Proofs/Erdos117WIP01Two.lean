/-
  Erdős Problem #117 — Covering Groups by Abelian Subgroups: the collapse at
  `n = 2` and the second exact value `h(2) = 1` (0-axiom).

  Companion to `Erdos117Problem.lean` / `Erdos117WIP01.lean` /
  `Erdos117WIP01Mono.lean` / `Erdos117WIP01Cover.lean`.  The parent defines
  `h(n) = abelianCoverNumber n = sInf {k | every finite group with the
  n-commuting property is covered by k abelian subgroups}` and states Pyber's
  exponential bounds `c₁ⁿ < h(n) < c₂ⁿ` only in prose.  Prior companions pin
  `h(0) = 0`, `h(1) = 1`, the closure theory of the property, monotonicity of
  `h`, and the terminal-segment structure of the covering set.

  This file settles the next rung of the ladder: **`h(2) = 1`**.  The reason is
  a genuine (if small) piece of group theory: in ANY non-abelian group, a single
  non-commuting pair `a, b` already spawns a *three-element pairwise
  non-commuting set* `{a, b, a*b}` — a 3-clique in the non-commuting graph.
  (`a` and `a*b` commute iff `a*b = b*a`, by cancellation; likewise `b` and
  `a*b`.)  Consequently the `2`-commuting property — "every 3-subset contains a
  commuting pair" — already forces the group to be abelian, exactly like the
  `1`-commuting property: the hierarchy COLLAPSES at `n = 2`.  One abelian
  subgroup (the whole group) then covers, and `h(2) = 1` unconditionally.

  Main results (all axiom-free — `#print axioms` = propext/Classical.choice/Quot.sound):

  * `exists_three_pairwise_noncommuting` : a non-abelian group contains a
                                        3-element subset with NO distinct
                                        commuting pair (`{a, b, a*b}`).
  * `hasNCommutingProperty_two_iff`   : the `2`-commuting property is *exactly*
                                        commutativity.
  * `hasNCommutingProperty_two_iff_one` : the `n = 2` and `n = 1` properties
                                        coincide — the first collapse of the
                                        hierarchy.
  * `abelianCoverNumber_two`          : **`h(2) = 1`** — the second exact value
                                        of the covering number.
  * `abelianCoverNumber_one_eq_two`   : `h(1) = h(2)` — the ladder is flat
                                        across the collapse.

  Where the collapse STOPS: at `n = 3` the property is strictly weaker than
  commutativity.  The quaternion group `Q₈` is non-abelian yet has the
  `3`-commuting property — its non-commuting graph has clique number 3, since
  any clique picks at most one element from each of `{±i}, {±j}, {±k}` — and
  needs three abelian subgroups (`⟨i⟩ ∪ ⟨j⟩ ∪ ⟨k⟩` covers; two cannot, as
  `4 + 4 - |intersection ⊇ {±1}| ≤ 6 < 8`).  So `h(3) ≥ 3`: the first
  genuinely non-abelian threshold, left for a future session.  The open
  Erdős #117 (the exact exponential base) and Pyber's bounds are untouched.

  0 axioms, 0 sorries.
-/

import Mathlib
import Proofs.Erdos117Problem
import Proofs.Erdos117WIP01

/-- **A non-abelian group contains three pairwise non-commuting elements.**
    Given `a * b ≠ b * a`, the subset `{a, b, a * b}` has cardinality 3 and no
    distinct commuting pair:

    * `a, b` do not commute by hypothesis;
    * `a, a*b` commute iff `a*(a*b) = (a*b)*a` iff (left-cancelling `a`)
      `a*b = b*a` — excluded;
    * `b, a*b` commute iff `b*(a*b) = (a*b)*b` iff (right-cancelling `b`)
      `b*a = a*b` — excluded.

    Distinctness is automatic: `a = b` would commute, `a = a*b` forces `b = 1`
    (central), `b = a*b` forces `a = 1` (central).  This is the 3-clique in the
    non-commuting graph that every non-abelian group carries. -/
theorem exists_three_pairwise_noncommuting {G : Type*} [Group G]
    (h : ∃ a b : G, a * b ≠ b * a) :
    ∃ S : Finset G, 2 < S.card ∧
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x * y ≠ y * x := by
  classical
  obtain ⟨a, b, hab⟩ := h
  -- The three pairwise non-commutation facts (each by cancellation).
  have hab' : a * (a * b) ≠ (a * b) * a := fun hc =>
    hab (mul_left_cancel (by rw [hc, mul_assoc]))
  have hbb' : b * (a * b) ≠ (a * b) * b := fun hc =>
    hab (mul_right_cancel (by rw [← mul_assoc] at hc; exact hc)).symm
  -- Distinctness of the three elements.
  have hne_ab : a ≠ b := fun hc => hab (by rw [hc])
  have hb1 : b ≠ 1 := fun hc => hab (by rw [hc, mul_one, one_mul])
  have ha1 : a ≠ 1 := fun hc => hab (by rw [hc, mul_one, one_mul])
  have hne_a_ab : a ≠ a * b := fun hc =>
    hb1 (mul_left_cancel (a := a) (by rw [mul_one]; exact hc)).symm
  have hne_b_ab : b ≠ a * b := fun hc =>
    ha1 (mul_right_cancel (b := b) (by rw [one_mul]; exact hc)).symm
  refine ⟨{a, b, a * b}, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hne_ab, hne_a_ab]),
      Finset.card_insert_of_notMem (by simp [hne_b_ab]), Finset.card_singleton]
    omega
  · intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact absurd rfl hxy
    · exact hab
    · exact hab'
    · exact fun hc => hab hc.symm
    · exact absurd rfl hxy
    · exact hbb'
    · exact fun hc => hab' hc.symm
    · exact fun hc => hbb' hc.symm
    · exact absurd rfl hxy

/-- **The `2`-commuting property is exactly commutativity.**  Forward: a
    non-abelian group carries a 3-element pairwise non-commuting subset
    (`exists_three_pairwise_noncommuting`), which violates the property at
    threshold `2`.  Backward: in a commutative group any subset of size `> 2`
    has two distinct (hence commuting) elements.  So the `n = 2` case adds
    nothing over `n = 1` — the hierarchy's first collapse. -/
theorem hasNCommutingProperty_two_iff {G : Type*} [Group G] :
    HasNCommutingProperty G 2 ↔ ∀ x y : G, x * y = y * x := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    obtain ⟨S, hcard, hnc⟩ := exists_three_pairwise_noncommuting hc
    obtain ⟨x, y, hx, hy, hxy, hcomm⟩ := h S hcard
    exact hnc x hx y hy hxy hcomm
  · intro h S hS
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      Finset.one_lt_card.mp (lt_trans one_lt_two hS)
    exact ⟨x, y, hx, hy, hxy, h x y⟩

/-- **The `n = 2` and `n = 1` commuting properties coincide.**  Both are exactly
    commutativity (`hasNCommutingProperty_two_iff`,
    `hasNCommutingProperty_one_iff`).  Note the contrast with the definitional
    monotonicity (`hasNCommutingProperty_mono` gives only `1`-property ⟹
    `2`-property): the reverse implication is the group-theoretic content.  The
    coincidence STOPS at `n = 3`, where `Q₈` is a non-abelian group with the
    `3`-commuting property. -/
theorem hasNCommutingProperty_two_iff_one {G : Type*} [Group G] :
    HasNCommutingProperty G 2 ↔ HasNCommutingProperty G 1 :=
  hasNCommutingProperty_two_iff.trans hasNCommutingProperty_one_iff.symm

/-- **`h(2) = 1`.**  A group with the `2`-commuting property is abelian
    (`hasNCommutingProperty_two_iff`), so the single subgroup `⊤` covers it:
    `1` is in the covering set and `h(2) ≤ 1`.  Conversely `0` is not in the
    set (the empty family cannot cover `PUnit`, which has the `2`-commuting
    property), and the set is nonempty, so `h(2) ≥ 1`.  Together with
    `abelianCoverNumber_one` this makes the ladder `h(0) = 0, h(1) = h(2) = 1`
    — flat across the collapse — before Pyber's exponential growth takes over. -/
theorem abelianCoverNumber_two : abelianCoverNumber 2 = 1 := by
  -- As in `abelianCoverNumber_one`: `abelianCoverNumber` quantifies over
  -- `Type*`, so witnesses are built inline at the set's fixed universe.
  unfold abelianCoverNumber
  apply le_antisymm
  · -- h(2) ≤ 1 : the single abelian subgroup `⊤` covers any group with the
    -- `2`-commuting property (that group is abelian).
    apply Nat.sInf_le
    intro G _ _ hprop
    exact ⟨fun _ => ⊤,
      fun _ x y _ _ => hasNCommutingProperty_two_iff.mp hprop x y,
      fun g => ⟨0, Subgroup.mem_top g⟩⟩
  · -- h(2) ≥ 1 : `0` is not in the covering set, and the set is nonempty.
    rw [Nat.one_le_iff_ne_zero, Ne, Nat.sInf_eq_zero]
    push_neg
    refine ⟨fun hmem => ?_, ?_⟩
    · -- `0 ∈` set would cover `PUnit` by an empty family of subgroups.
      simp only [Set.mem_setOf_eq] at hmem
      obtain ⟨H, _, hcov⟩ :=
        hmem PUnit (commGroup_hasNCommutingProperty one_le_two)
      obtain ⟨i, _⟩ := hcov PUnit.unit
      exact i.elim0
    · -- The set is nonempty: `1` belongs to it.
      refine ⟨1, ?_⟩
      intro G _ _ hprop
      exact ⟨fun _ => ⊤,
        fun _ x y _ _ => hasNCommutingProperty_two_iff.mp hprop x y,
        fun g => ⟨0, Subgroup.mem_top g⟩⟩

/-- **`h(1) = h(2)`.**  The covering number is flat across the collapse: both
    thresholds constrain exactly the abelian groups, and one subgroup covers.
    (First strict growth can only occur at `n = 3` or later; `Q₈` shows
    `h(3) ≥ 3` — the covering number jumps once genuinely non-abelian groups
    satisfy the property.) -/
theorem abelianCoverNumber_one_eq_two :
    abelianCoverNumber 1 = abelianCoverNumber 2 := by
  rw [abelianCoverNumber_one, abelianCoverNumber_two]

-- Axiom audit: everything above is axiom-free
-- (expected: propext, Classical.choice, Quot.sound only).
#print axioms exists_three_pairwise_noncommuting
#print axioms hasNCommutingProperty_two_iff
#print axioms hasNCommutingProperty_two_iff_one
#print axioms abelianCoverNumber_two
#print axioms abelianCoverNumber_one_eq_two
