/-
  Erdős Problem #117 — Covering Groups by Abelian Subgroups:
  the first nontrivial lower bound — `h(n) ≥ 3` for all `n ≥ 3` (0-axiom).

  Companion to `Erdos117Problem.lean` / `Erdos117WIP01.lean` /
  `Erdos117WIP01Mono.lean` / `Erdos117WIP01Cover.lean` / `Erdos117WIP01Two.lean`.
  The parent defines `h(n) = abelianCoverNumber n = sInf {k | CoversWithAbelian k n}`,
  where `CoversWithAbelian k n` says `k` abelian subgroups suffice to cover *every*
  finite group with the `n`-commuting property.  Prior companions pin the ladder
  `h(0) = 0`, `h(1) = h(2) = 1` (the `n = 2` collapse: the 2-commuting property
  forces commutativity), monotonicity, and upward closure of the covering set.

  This file proves the ladder **jumps past `2` at `n = 3`**, in two steps.

  **1. No group is the union of two proper subgroups** (a classical fact:
  `x ∉ H`, `y ∉ K` force `xy ∉ H ∪ K`).  Hence a cover by two *abelian*
  subgroups forces one of them to be `⊤`, i.e. the group is abelian
  (`comm_of_two_abelian_cover`).  Note no counting, finiteness, or Lagrange is
  needed — this kills budget `2` in complete generality.

  **2. The quaternion group `Q₈` is a non-abelian group with the 3-commuting
  property.**  `Q₈ = QuaternionGroup 2` (Mathlib) has 8 elements: the central
  `±1` and the six units `±i, ±j, ±k` lying on three "axes" (cyclic subgroups)
  `⟨i⟩, ⟨j⟩, ⟨k⟩`.  Any subset of size `> 3` either meets the center (a central
  element commutes with everything) or has, by pigeonhole, two elements on one
  axis — and those commute.  So every 4-subset contains a distinct commuting
  pair (`quaternionGroup_hasNCommutingProperty_three`, verified by `decide` —
  a kernel-checked finite computation over all subsets of `Q₈`, no
  `Lean.ofReduceBool`).  Yet `i·j = k ≠ -k = j·i`, so `Q₈` is not abelian.

  Since the `n`-commuting property is monotone in `n`, `Q₈` witnesses
  `¬ CoversWithAbelian 2 n` for every `n ≥ 3` (`not_coversWithAbelian_two`),
  and with upward closure of the covering set this yields the conditional
  lower bound `h(n) ≥ 3` for all `n ≥ 3` — conditional exactly on the covering
  set being nonempty (= Pyber's unformalized upper bound; with `sInf ∅ = 0`
  an ill-defined `h(n)` is `0`).  In particular `h(2) < h(3)`: the first
  strict increase of the ladder after `h(0) < h(1)`, and the first point where
  the covering number separates from `1`.

  Main results (all axiom-free — `#print axioms` = propext/Classical.choice/Quot.sound):

  * `eq_top_or_eq_top_of_cover`       : a group is never the union of two proper
                                        subgroups.
  * `comm_of_two_abelian_cover`       : two abelian subgroups cover ⟹ the group
                                        is abelian.
  * `quaternionGroup_not_comm`        : `Q₈` is not abelian.
  * `quaternionGroup_hasNCommutingProperty_three` : `Q₈` has the 3-commuting
                                        property (noncommuting-graph clique
                                        number 3).
  * `hasNCommutingProperty_three_not_comm` : the `n = 2` collapse is **sharp** —
                                        the 3-commuting property does not force
                                        commutativity.
  * `not_coversWithAbelian_two`       : for `n ≥ 3`, budget `2` never covers
                                        (`Q₈`, lifted to any universe via `ULift`).
  * `not_coversWithAbelian_one`       : for `n ≥ 3`, budget `1` never covers.
  * `three_le_abelianCoverNumber`     : **`h(n) ≥ 3` for all `n ≥ 3`** whenever
                                        `h(n)` is well-defined.
  * `three_le_abelianCoverNumber_three` : `h(3) ≥ 3`.
  * `abelianCoverNumber_two_lt_three` : `h(2) < h(3)` — the ladder's first
                                        strict jump past `1` (conditional).
  * `abelianCoverNumber_three_eq_zero_or_three_le` : unconditionally, `h(3)` is
                                        `0` (ill-defined fallback) or `≥ 3`.

  The open Erdős #117 (the exact exponential base) and Pyber's bounds are untouched.
  `h(3) ≤ 3` (hence `h(3) = 3`) would need a uniform 3-cover for *every*
  3-commuting group — a classification-strength statement, not attempted here.

  0 axioms, 0 sorries.
-/

import Mathlib
import Proofs.Erdos117Problem
import Proofs.Erdos117WIP01
import Proofs.Erdos117WIP01Mono
import Proofs.Erdos117WIP01Cover
import Proofs.Erdos117WIP01Two

/- The universe of the ambient groups (see `Erdos117WIP01Mono.lean`):
   `CoversWithAbelian`/`abelianCoverNumber` are universe-polymorphic, so every
   occurrence below is pinned to the same `u`.  The finite witness `Q₈` lives in
   `Type 0` and is transported into `Type u` by `ULift`. -/
universe u

/- ## 1. No group is the union of two proper subgroups -/

/-- **A group is never the union of two proper subgroups.**  If every element
    lies in `H` or `K`, then `H = ⊤` or `K = ⊤`.  Classical argument: otherwise
    pick `x ∉ H` (so `x ∈ K`) and `y ∉ K` (so `y ∈ H`); then `x * y` can lie in
    neither — `x * y ∈ H` would give `x = (x * y) * y⁻¹ ∈ H`, and `x * y ∈ K`
    would give `y = x⁻¹ * (x * y) ∈ K`. -/
theorem eq_top_or_eq_top_of_cover {G : Type*} [Group G] {H K : Subgroup G}
    (hcov : ∀ g : G, g ∈ H ∨ g ∈ K) : H = ⊤ ∨ K = ⊤ := by
  by_contra hne
  push_neg at hne
  obtain ⟨hH, hK⟩ := hne
  obtain ⟨x, hx⟩ : ∃ x, x ∉ H := by
    by_contra hall
    push_neg at hall
    exact hH ((Subgroup.eq_top_iff' H).mpr hall)
  obtain ⟨y, hy⟩ : ∃ y, y ∉ K := by
    by_contra hall
    push_neg at hall
    exact hK ((Subgroup.eq_top_iff' K).mpr hall)
  have hxK : x ∈ K := (hcov x).resolve_left hx
  have hyH : y ∈ H := (hcov y).resolve_right hy
  rcases hcov (x * y) with hxy | hxy
  · exact hx (by simpa using H.mul_mem hxy (H.inv_mem hyH))
  · exact hy (by simpa using K.mul_mem (K.inv_mem hxK) hxy)

/-- **A cover by two abelian subgroups forces the group abelian.**  By
    `eq_top_or_eq_top_of_cover` one of the two subgroups is `⊤`, and an abelian
    `⊤` means all elements commute.  This kills covering budget `2` for every
    non-abelian group — with no finiteness or counting whatsoever. -/
theorem comm_of_two_abelian_cover {G : Type*} [Group G] {H : Fin 2 → Subgroup G}
    (hAb : ∀ i, IsAbelianSubgroup G (H i)) (hCov : ∀ g : G, ∃ i, g ∈ H i)
    (x y : G) : x * y = y * x := by
  have hcov2 : ∀ g : G, g ∈ H 0 ∨ g ∈ H 1 := by
    intro g
    obtain ⟨i, hi⟩ := hCov g
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  rcases eq_top_or_eq_top_of_cover hcov2 with htop | htop
  · have h0 := hAb 0
    rw [htop] at h0
    exact h0 x y (Subgroup.mem_top x) (Subgroup.mem_top y)
  · have h1 := hAb 1
    rw [htop] at h1
    exact h1 x y (Subgroup.mem_top x) (Subgroup.mem_top y)

/- ## 2. The witness: `Q₈` is non-abelian with the 3-commuting property -/

/-- **`Q₈` is not abelian**: `i * j ≠ j * i` (concretely `a 1 * xa 0 ≠ xa 0 * a 1`
    in Mathlib's presentation of `QuaternionGroup 2`). -/
theorem quaternionGroup_not_comm :
    ∃ x y : QuaternionGroup 2, x * y ≠ y * x :=
  ⟨QuaternionGroup.a 1, QuaternionGroup.xa 0, by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
/-- **`Q₈` has the 3-commuting property**: every subset of size `> 3` contains
    two distinct commuting elements.  Mathematically: a 4-subset either meets
    the center `{±1}` or, by pigeonhole, contains two elements of one of the
    three cyclic "axes" `⟨i⟩, ⟨j⟩, ⟨k⟩` — a commuting pair either way; so the
    noncommuting graph of `Q₈` has clique number `3` (the clique `{i, j, k}` is
    realized, per `exists_three_pairwise_noncommuting`).  Verified by a
    kernel-checked finite computation (`decide`) over all `2⁸` subsets — no
    `Lean.ofReduceBool` involved. -/
theorem quaternionGroup_hasNCommutingProperty_three :
    HasNCommutingProperty (QuaternionGroup 2) 3 := by
  unfold HasNCommutingProperty
  decide

/-- **The `n = 2` collapse is sharp.**  `hasNCommutingProperty_two_iff` shows the
    2-commuting property forces commutativity; at threshold `3` this fails —
    `Q₈` is a finite non-abelian group with the 3-commuting property. -/
theorem hasNCommutingProperty_three_not_comm :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G),
      HasNCommutingProperty G 3 ∧ ∃ x y : G, x * y ≠ y * x :=
  ⟨QuaternionGroup 2, inferInstance, inferInstance,
    quaternionGroup_hasNCommutingProperty_three, quaternionGroup_not_comm⟩

/- ## 3. The lower bound `h(n) ≥ 3` for `n ≥ 3` -/

/-- **Budget `2` never covers at any threshold `n ≥ 3`.**  The witness is
    `ULift Q₈` (transported to universe `u`; the property transfers along the
    isomorphism `MulEquiv.ulift` and up the threshold by monotonicity).  A
    2-abelian-cover of it would force it abelian (`comm_of_two_abelian_cover`),
    contradicting `i * j ≠ j * i`. -/
theorem not_coversWithAbelian_two {n : ℕ} (hn : 3 ≤ n) :
    ¬ CoversWithAbelian.{u} 2 n := by
  intro h
  obtain ⟨H, hAb, hCov⟩ := h (ULift.{u} (QuaternionGroup 2))
    (hasNCommutingProperty_mono hn
      (hasNCommutingProperty_of_mulEquiv MulEquiv.ulift.symm
        quaternionGroup_hasNCommutingProperty_three))
  obtain ⟨x, y, hxy⟩ := quaternionGroup_not_comm
  have hcomm := comm_of_two_abelian_cover hAb hCov (ULift.up x) (ULift.up y)
  -- multiplication on `ULift` is componentwise by definition, so applying
  -- `ULift.down` to the commutation in `ULift Q₈` lands on commutation in `Q₈`.
  exact hxy (congrArg ULift.down hcomm)

/-- **Budget `1` never covers at any threshold `n ≥ 3`** — upward closure of the
    covering set reduces this to `not_coversWithAbelian_two`.  (A single abelian
    cover would of course also force commutativity directly.) -/
theorem not_coversWithAbelian_one {n : ℕ} (hn : 3 ≤ n) :
    ¬ CoversWithAbelian.{u} 1 n :=
  fun h => not_coversWithAbelian_two hn (coversWithAbelian_upward one_le_two h)

/-- **`h(n) ≥ 3` for every `n ≥ 3`** — whenever `h(n)` is well-defined (the
    covering set is nonempty rather than the `sInf ∅ = 0` fallback; for `n ≥ 3`
    nonemptiness is exactly Pyber's unformalized upper bound).  Proof: `h(n)` is
    a member of the covering set (`Nat.sInf_mem`), so `h(n) ≤ 2` would put `2`
    in the set by upward closure — contradicting `not_coversWithAbelian_two`. -/
theorem three_le_abelianCoverNumber {n : ℕ} (hn : 3 ≤ n)
    (hne : ∃ k, CoversWithAbelian.{u} k n) :
    3 ≤ abelianCoverNumber.{u} n := by
  by_contra hlt
  push_neg at hlt
  have hneSet : {k | CoversWithAbelian.{u} k n}.Nonempty := hne
  have hmem : CoversWithAbelian.{u} (abelianCoverNumber.{u} n) n := Nat.sInf_mem hneSet
  have hle : abelianCoverNumber.{u} n ≤ 2 := by omega
  exact not_coversWithAbelian_two hn (coversWithAbelian_upward hle hmem)

/-- **`h(3) ≥ 3`** — the threshold case `n = 3`. -/
theorem three_le_abelianCoverNumber_three
    (hne : ∃ k, CoversWithAbelian.{u} k 3) :
    3 ≤ abelianCoverNumber.{u} 3 :=
  three_le_abelianCoverNumber (le_refl 3) hne

/-- **The ladder's first strict jump past `1`: `h(2) < h(3)`** (conditional on
    `h(3)` being well-defined).  With `h(0) = 0 < h(1) = h(2) = 1` from prior
    companions, the known exact shape of the ladder is now
    `0, 1, 1, ≥3, …` — the covering number separates from `1` exactly at the
    threshold where the commuting property stops forcing commutativity. -/
theorem abelianCoverNumber_two_lt_three
    (hne : ∃ k, CoversWithAbelian.{u} k 3) :
    abelianCoverNumber.{u} 2 < abelianCoverNumber.{u} 3 := by
  have h2 : abelianCoverNumber.{u} 2 = 1 := abelianCoverNumber_two
  have h3 := three_le_abelianCoverNumber_three hne
  omega

/-- **Unconditional dichotomy for `h(3)`**: either the covering set is empty and
    `h(3) = 0` (the `sInf ∅ = 0` fallback — ruled out mathematically by Pyber's
    upper bound, which is not formalized), or `h(3) ≥ 3`.  In no case is
    `h(3) ∈ {1, 2}`. -/
theorem abelianCoverNumber_three_eq_zero_or_three_le :
    abelianCoverNumber.{u} 3 = 0 ∨ 3 ≤ abelianCoverNumber.{u} 3 := by
  by_cases hne : ∃ k, CoversWithAbelian.{u} k 3
  · exact Or.inr (three_le_abelianCoverNumber_three hne)
  · left
    rw [abelianCoverNumber_eq_sInf]
    exact Nat.sInf_eq_zero.mpr
      (Or.inr (Set.not_nonempty_iff_eq_empty.mp hne))

/- ## Axiom audit -/

#print axioms eq_top_or_eq_top_of_cover
#print axioms comm_of_two_abelian_cover
#print axioms quaternionGroup_hasNCommutingProperty_three
#print axioms not_coversWithAbelian_two
#print axioms three_le_abelianCoverNumber
#print axioms abelianCoverNumber_two_lt_three
#print axioms abelianCoverNumber_three_eq_zero_or_three_le
