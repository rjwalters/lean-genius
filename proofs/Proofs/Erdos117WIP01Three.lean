/-
  Erdős Problem #117 — Covering Groups by Abelian Subgroups: the quaternion
  group `Q₈` breaks the collapse at `n = 3` and forces the lower bound
  `h(3) ≥ 3` (0-axiom).

  Companion to `Erdos117Problem.lean` / `Erdos117WIP01.lean` /
  `Erdos117WIP01Mono.lean` / `Erdos117WIP01Cover.lean` /
  `Erdos117WIP01Two.lean`.  Prior companions pin the ladder
  `h(0) = 0, h(1) = h(2) = 1`: the `1`- and `2`-commuting properties both
  collapse to commutativity, so a single abelian subgroup (the whole group)
  covers.  This file shows the collapse ENDS at `n = 3` — the first threshold
  where genuinely non-abelian groups appear — and quantifies the cost: the
  covering budget must jump from `1` to at least `3`.

  The witness is the quaternion group `Q₈ = QuaternionGroup 2` (Mathlib's
  dicyclic family at `n = 2`; order `8`, elements `±1, ±i, ±j, ±k`):

  * `Q₈` HAS the `3`-commuting property: its non-commuting graph has clique
    number `3`.  Any `4` elements either meet the center `{±1}` (which
    commutes with everything) or hit one of the three cosets
    `{±i}, {±j}, {±k}` twice — and each such pair commutes (`i·(-i) = (-i)·i`).
    Verified by kernel `decide` over all `2⁸ = 256` subsets (no
    `native_decide`, no `Lean.ofReduceBool`).
  * `Q₈` is non-abelian (`ij = k ≠ -k = ji`), so it needs MORE than one
    abelian subgroup — and in fact more than two: a group is never the union
    of two proper subgroups (`subgroup_eq_top_or_eq_top_of_cover`, the
    classical exchange argument), and an abelian subgroup of a non-abelian
    group is always proper.
  * Three abelian subgroups DO cover: `⟨i⟩ ∪ ⟨j⟩ ∪ ⟨k⟩ = Q₈` — each cyclic of
    order `4`, exhibited by explicit powers.  So the `Q₈` witness is tight.

  Main results (all axiom-free — `#print axioms` = propext/Classical.choice/
  Quot.sound):

  * `quaternionGroup_not_commute`      : `a 1 * xa 0 ≠ xa 0 * a 1` in `Q₈`.
  * `hasNCommutingProperty_quaternionGroup_three` : `Q₈` has the `3`-commuting
                                        property (kernel `decide`).
  * `not_hasNCommutingProperty_quaternionGroup_two` : `Q₈` fails the
                                        `2`-commuting property — so the
                                        inclusion "`2`-property ⟹
                                        `3`-property" is STRICT at `Q₈`.
  * `subgroup_eq_top_or_eq_top_of_cover` : a group covered by two subgroups is
                                        one of them (no group is a union of
                                        two proper subgroups).
  * `quaternionGroup_no_two_abelian_cover` : no two abelian subgroups cover
                                        `Q₈`.
  * `quaternionGroup_covered_by_three` : three abelian subgroups cover `Q₈` —
                                        the witness is tight.
  * `three_le_of_coversWithAbelian_three` : **every uniform covering budget
                                        for `n = 3` is `≥ 3`** — the
                                        unconditional form of the lower bound,
                                        via `ULift Q₈` in every universe.
  * `three_le_abelianCoverNumber_three` : `h(3) ≥ 3`, conditional only on the
                                        well-definedness of `h(3)` (the
                                        defining set being nonempty — Pyber's
                                        upper bound, unformalized).
  * `abelianCoverNumber_two_lt_three` : `h(2) < h(3)` under the same
                                        hypothesis — the FIRST STRICT JUMP of
                                        the ladder: `h` is not constant, the
                                        growth phenomenon of Erdős #117 has
                                        begun.

  What remains open/deep: Pyber's exponential bounds `c₁ⁿ < h(n) < c₂ⁿ` and
  the exact base of growth (the actual Erdős #117 question) are untouched;
  even the nonemptiness hypothesis above (a uniform bound for `n = 3`) is a
  real theorem beyond this file's elementary scope.

  0 axioms, 0 sorries.
-/

import Mathlib
import Proofs.Erdos117Problem
import Proofs.Erdos117WIP01
import Proofs.Erdos117WIP01Mono
import Proofs.Erdos117WIP01Two
import Proofs.Erdos117WIP01Cover

/- The ambient-group universe: `abelianCoverNumber` and `CoversWithAbelian`
   are universe-polymorphic, and mixing universes in one statement produces
   the `.{u_1}` vs `.{u_3}` application-type mismatch.  All quantified
   statements below fix `u` explicitly; the `Q₈` witness enters every
   universe via `ULift`. -/
universe u

open QuaternionGroup

/-- **`Q₈` is non-abelian**: in Mathlib's presentation `a 1 * xa 0 = xa 3`
    while `xa 0 * a 1 = xa 1` (the relation `x⁻¹ a x = a⁻¹`).  In quaternion
    language: `i · j ≠ j · i`. -/
theorem quaternionGroup_not_commute :
    (a 1 : QuaternionGroup 2) * xa 0 ≠ xa 0 * a 1 := by decide

/-- **`Q₈` has the `3`-commuting property**: every subset of size `≥ 4`
    contains a distinct commuting pair.  Structurally: the center `{±1}`
    commutes with everything, and the six non-central elements fall into the
    three mutually-commuting pairs `{±i}, {±j}, {±k}`; four elements cannot
    avoid both the center and a repeated pair.  Verified exhaustively by
    kernel `decide` over all `256` subsets — pure kernel reduction, NOT
    `native_decide`, so no `Lean.ofReduceBool` enters the axiom trail. -/
set_option maxRecDepth 40000 in
theorem hasNCommutingProperty_quaternionGroup_three :
    HasNCommutingProperty (QuaternionGroup 2) 3 := by
  unfold HasNCommutingProperty
  decide

/-- **`Q₈` fails the `2`-commuting property** (it is non-abelian, and the
    `2`-property is exactly commutativity by `hasNCommutingProperty_two_iff`).
    Together with `hasNCommutingProperty_quaternionGroup_three` this shows the
    monotone inclusion "`2`-property ⟹ `3`-property"
    (`hasNCommutingProperty_mono`) is STRICT: `Q₈` separates the thresholds,
    which is precisely why the hierarchy stops collapsing at `n = 3`. -/
theorem not_hasNCommutingProperty_quaternionGroup_two :
    ¬ HasNCommutingProperty (QuaternionGroup 2) 2 := fun h =>
  quaternionGroup_not_commute (hasNCommutingProperty_two_iff.mp h _ _)

/-- **No group is the union of two proper subgroups.**  If every element lies
    in `H` or `K`, then `H = ⊤` or `K = ⊤`.  The classical exchange argument:
    if neither contains the other, pick `x ∈ H \ K` and `y ∈ K \ H`; the
    product `x * y` can lie in neither — in `H` it would drag `y` in
    (`y = x⁻¹ · (x·y)`), in `K` it would drag `x` in (`x = (x·y) · y⁻¹`). -/
theorem subgroup_eq_top_or_eq_top_of_cover {G : Type*} [Group G]
    {H K : Subgroup G} (hcov : ∀ g : G, g ∈ H ∨ g ∈ K) : H = ⊤ ∨ K = ⊤ := by
  by_cases hHK : H ≤ K
  · right
    rw [eq_top_iff]
    exact fun g _ => (hcov g).elim (fun hg => hHK hg) id
  by_cases hKH : K ≤ H
  · left
    rw [eq_top_iff]
    exact fun g _ => (hcov g).elim id fun hg => hKH hg
  exfalso
  obtain ⟨x, hxH, hxK⟩ := SetLike.not_le_iff_exists.mp hHK
  obtain ⟨y, hyK, hyH⟩ := SetLike.not_le_iff_exists.mp hKH
  rcases hcov (x * y) with hxy | hxy
  · exact hyH (by simpa using H.mul_mem (H.inv_mem hxH) hxy)
  · exact hxK (by simpa using K.mul_mem hxy (K.inv_mem hyK))

/-- **Two abelian subgroups cannot cover a non-abelian group.**  A covering
    pair forces one subgroup to be everything
    (`subgroup_eq_top_or_eq_top_of_cover`), and an abelian `⊤` makes the whole
    group commute — contradicting the witness pair. -/
theorem not_abelian_cover_two {G : Type*} [Group G] {x y : G}
    (hxy : x * y ≠ y * x) {H K : Subgroup G}
    (hH : IsAbelianSubgroup G H) (hK : IsAbelianSubgroup G K)
    (hcov : ∀ g : G, g ∈ H ∨ g ∈ K) : False := by
  rcases subgroup_eq_top_or_eq_top_of_cover hcov with rfl | rfl
  · exact hxy (hH x y (Subgroup.mem_top x) (Subgroup.mem_top y))
  · exact hxy (hK x y (Subgroup.mem_top x) (Subgroup.mem_top y))

/-- **No two abelian subgroups cover `Q₈`** — the specialization of
    `not_abelian_cover_two` at the witness `i·j ≠ j·i`.  (Counting confirms
    it: abelian subgroups of `Q₈` have order `≤ 4`, and two of them share the
    identity, covering at most `4 + 4 - 1 = 7 < 8` elements.) -/
theorem quaternionGroup_no_two_abelian_cover
    {H K : Subgroup (QuaternionGroup 2)}
    (hH : IsAbelianSubgroup (QuaternionGroup 2) H)
    (hK : IsAbelianSubgroup (QuaternionGroup 2) K) :
    ¬ ∀ g : QuaternionGroup 2, g ∈ H ∨ g ∈ K := fun hcov =>
  not_abelian_cover_two quaternionGroup_not_commute hH hK hcov

/-- **Three abelian subgroups DO cover `Q₈`**: the three maximal cyclic
    subgroups `⟨i⟩, ⟨j⟩, ⟨k⟩` — in Mathlib's presentation
    `⟨a 1⟩ = {1, a 1, a 2, a 3}`, `⟨xa 0⟩ = {1, xa 0, a 2, xa 2}`,
    `⟨xa 1⟩ = {1, xa 1, a 2, xa 3}` — each cyclic of order `4`, hence abelian
    (`isAbelianSubgroup_zpowers`), jointly exhausting all `8` elements by
    explicit powers.  Together with `quaternionGroup_no_two_abelian_cover`
    this pins `Q₈`'s own minimal abelian covering number at exactly `3`. -/
theorem quaternionGroup_covered_by_three :
    ∃ H : Fin 3 → Subgroup (QuaternionGroup 2),
      (∀ i, IsAbelianSubgroup (QuaternionGroup 2) (H i)) ∧
      ∀ g : QuaternionGroup 2, ∃ i, g ∈ H i := by
  refine ⟨![Subgroup.zpowers (a 1), Subgroup.zpowers (xa 0),
      Subgroup.zpowers (xa 1)], fun i => ?_, fun g => ?_⟩
  · fin_cases i <;> exact isAbelianSubgroup_zpowers _
  · rcases g with i | i <;> fin_cases i
    · exact ⟨0, Subgroup.mem_zpowers_iff.mpr ⟨0, by decide⟩⟩
    · exact ⟨0, Subgroup.mem_zpowers_iff.mpr ⟨1, by decide⟩⟩
    · exact ⟨0, Subgroup.mem_zpowers_iff.mpr ⟨2, by decide⟩⟩
    · exact ⟨0, Subgroup.mem_zpowers_iff.mpr ⟨3, by decide⟩⟩
    · exact ⟨1, Subgroup.mem_zpowers_iff.mpr ⟨1, by decide⟩⟩
    · exact ⟨2, Subgroup.mem_zpowers_iff.mpr ⟨1, by decide⟩⟩
    · exact ⟨1, Subgroup.mem_zpowers_iff.mpr ⟨3, by decide⟩⟩
    · exact ⟨2, Subgroup.mem_zpowers_iff.mpr ⟨3, by decide⟩⟩

/-- **Every uniform covering budget for `n = 3` is at least `3`** — the
    unconditional core of the lower bound `h(3) ≥ 3`.  If `k` abelian
    subgroups covered every finite group with the `3`-commuting property,
    then in particular they would cover `ULift Q₈` (the witness transported
    into the ambient universe via `MulEquiv.ulift`,
    `hasNCommutingProperty_of_mulEquiv`).  But an empty family covers
    nothing, and one or two abelian subgroups cannot cover a non-abelian
    group (`not_abelian_cover_two`) — so `k ≥ 3`. -/
theorem three_le_of_coversWithAbelian_three {k : ℕ}
    (h : CoversWithAbelian.{u} k 3) : 3 ≤ k := by
  by_contra hlt
  push_neg at hlt
  have hQ : HasNCommutingProperty (ULift.{u} (QuaternionGroup 2)) 3 :=
    hasNCommutingProperty_of_mulEquiv MulEquiv.ulift.symm
      hasNCommutingProperty_quaternionGroup_three
  obtain ⟨H, hab, hcov⟩ := h (ULift.{u} (QuaternionGroup 2)) hQ
  have hnc : (ULift.up (a 1) : ULift.{u} (QuaternionGroup 2)) * ULift.up (xa 0) ≠
      ULift.up (xa 0) * ULift.up (a 1) := fun hcontra =>
    quaternionGroup_not_commute (congrArg ULift.down hcontra)
  interval_cases k
  · obtain ⟨i, -⟩ := hcov 1
    exact i.elim0
  · refine not_abelian_cover_two hnc (hab 0) (hab 0) fun g => ?_
    obtain ⟨i, hi⟩ := hcov g
    fin_cases i
    exact Or.inl hi
  · refine not_abelian_cover_two hnc (hab 0) (hab 1) fun g => ?_
    obtain ⟨i, hi⟩ := hcov g
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi

/-- **`h(3) ≥ 3`**, conditional only on `h(3)` being well-defined — i.e. on
    the defining set `{k | CoversWithAbelian k 3}` being nonempty, which is
    Pyber's (unformalized, deep) upper-bound side.  Without nonemptiness
    `sInf ∅ = 0` would collapse the value, so the hypothesis is exactly the
    honest boundary of what this file proves; the membership fact it feeds on
    (`three_le_of_coversWithAbelian_three`) is unconditional. -/
theorem three_le_abelianCoverNumber_three
    (hne : ∃ k, CoversWithAbelian.{u} k 3) :
    3 ≤ abelianCoverNumber.{u} 3 := by
  rw [abelianCoverNumber_eq_sInf]
  exact three_le_of_coversWithAbelian_three (Nat.sInf_mem hne)

/-- **The first strict jump of the ladder: `h(2) < h(3)`** (under the same
    well-definedness hypothesis).  The exact values so far are
    `h(0) = 0, h(1) = h(2) = 1` (`abelianCoverNumber_two`), and now the
    budget triples at `n = 3`: `h` is NOT constant — the growth phenomenon
    that Erdős #117 asks to quantify (Pyber: exponential) genuinely starts
    here, at the quaternion group. -/
theorem abelianCoverNumber_two_lt_three
    (hne : ∃ k, CoversWithAbelian.{u} k 3) :
    abelianCoverNumber.{u} 2 < abelianCoverNumber.{u} 3 := by
  have h3 : 3 ≤ abelianCoverNumber.{u} 3 := three_le_abelianCoverNumber_three hne
  have h2 : abelianCoverNumber.{u} 2 = 1 := abelianCoverNumber_two
  omega

-- Axiom audit: everything above is axiom-free
-- (propext, Classical.choice, Quot.sound only — no Lean.ofReduceBool).
#print axioms quaternionGroup_not_commute
#print axioms hasNCommutingProperty_quaternionGroup_three
#print axioms not_hasNCommutingProperty_quaternionGroup_two
#print axioms subgroup_eq_top_or_eq_top_of_cover
#print axioms not_abelian_cover_two
#print axioms quaternionGroup_no_two_abelian_cover
#print axioms quaternionGroup_covered_by_three
#print axioms three_le_of_coversWithAbelian_three
#print axioms three_le_abelianCoverNumber_three
#print axioms abelianCoverNumber_two_lt_three
