/-
  Erdős Problem #117 — Covering Groups by Abelian Subgroups: foundational facts (0-axiom).

  Companion to `Erdos117Problem.lean`. That file defines the `n`-commuting
  property, abelian subgroups, and the covering number
  `h(n) = abelianCoverNumber n = sInf {k | every finite group with the
  n-commuting property is covered by k abelian subgroups}`, and states Pyber's
  exponential bounds `c₁ⁿ < h(n) < c₂ⁿ` only in prose. This file supplies the
  elementary, machine-checkable facts the parent leaves out — in particular the
  trivial base case `h(1) = 1` — while Pyber's deep bounds stay unformalized.

  Main results (all axiom-free — `#print axioms` = propext/Classical.choice/Quot.sound):

  * `not_hasNCommutingProperty_zero`  : no group has the `0`-commuting property
                                        (a singleton has no distinct pair).
  * `commGroup_hasNCommutingProperty` : every commutative group has the
                                        `n`-commuting property for all `n ≥ 1`.
  * `abelianCoverNumber_one`          : **`h(1) = 1`** — one abelian subgroup
                                        (the whole group, which is abelian by the
                                        `1`-commuting property) suffices, and zero
                                        never does.
  * `abelianCoverNumber_zero`         : **`h(0) = 0`** — the `0`-commuting property
                                        holds for no group, so the covering
                                        condition is vacuous and the empty family
                                        `Fin 0 → Subgroup G` witnesses `0 ∈` the
                                        covering set.
  * `hasNCommutingProperty_one_iff`   : the `1`-commuting property is *exactly*
                                        commutativity (both directions).
  * `abelianCoverNumber_zero_lt_one`  : **`h(0) < h(1)`** — the covering number
                                        already jumps at the base of the ladder.

  Structural theory of the property itself (closure properties, all axiom-free):

  * `hasNCommutingProperty_of_injective` : the property transfers along injective
                                        homomorphisms (it only weakens under
                                        embedding into a larger group).
  * `hasNCommutingProperty_subgroup`    : subgroups inherit the property
                                        (hereditary).
  * `hasNCommutingProperty_of_mulEquiv` : the property is an isomorphism invariant.
  * `hasNCommutingProperty_of_card_le`  : every finite group has the property once
                                        `n` reaches its order (eventually universal).

  The open Erdős #117 (the exact base of the exponential growth of `h(n)`) and
  Pyber's bounds are untouched.
-/

import Mathlib
import Proofs.Erdos117Problem

/-- **No group has the `0`-commuting property.** The property at `n = 0` demands a
    distinct commuting pair inside *every* nonempty subset, but the singleton `{1}`
    (card `1 > 0`) has no two distinct elements. -/
theorem not_hasNCommutingProperty_zero {G : Type*} [Group G] :
    ¬ HasNCommutingProperty G 0 := by
  intro h
  obtain ⟨x, y, hx, hy, hxy, _⟩ := h {1} (by simp)
  simp only [Finset.mem_singleton] at hx hy
  exact hxy (hx.trans hy.symm)

/-- **Every commutative group has the `n`-commuting property for `n ≥ 1`.**
    Immediate from the `n = 1` case (any subset of size `> 1` has two distinct,
    hence commuting, elements) and monotonicity of the property in `n`. -/
theorem commGroup_hasNCommutingProperty {G : Type*} [CommGroup G] {n : ℕ}
    (hn : 1 ≤ n) : HasNCommutingProperty G n :=
  hasNCommutingProperty_mono hn commGroup_hasNCommutingProperty_one

/-- **The `1`-commuting property is exactly commutativity.** The forward
    direction is `commute_of_hasNCommutingProperty_one`; conversely, if every pair
    commutes then any subset of size `> 1` contains two distinct commuting
    elements, so the property holds. This pins down `h` at the base of the ladder:
    `HasNCommutingProperty G 1` characterises abelian groups. -/
theorem hasNCommutingProperty_one_iff {G : Type*} [Group G] :
    HasNCommutingProperty G 1 ↔ ∀ x y : G, x * y = y * x := by
  constructor
  · intro h x y
    exact commute_of_hasNCommutingProperty_one h x y
  · intro h S hS
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hS
    exact ⟨x, y, hx, hy, hxy, h x y⟩

/-- **`h(1) = 1`.** A group with the `1`-commuting property is abelian
    (`commute_of_hasNCommutingProperty_one`), so the single subgroup `⊤` — abelian
    and covering everything — witnesses `1 ∈` the covering set, giving `h(1) ≤ 1`.
    Conversely `0` is never in the set: an empty family `Fin 0 → Subgroup G` cannot
    cover the identity of the (nonempty) witness group `PUnit`, so `h(1) ≠ 0`. -/
theorem abelianCoverNumber_one : abelianCoverNumber 1 = 1 := by
  -- `abelianCoverNumber` quantifies over `Type*`, so the witnesses below must be
  -- built inline at the set's fixed universe (a factored `Type*` lemma would
  -- introduce a second, non-unifying universe).
  unfold abelianCoverNumber
  apply le_antisymm
  · -- h(1) ≤ 1 : the single abelian subgroup `⊤` covers any group with the
    -- `1`-commuting property (that group is abelian), so `1` is in the set.
    apply Nat.sInf_le
    intro G _ _ hprop
    exact ⟨fun _ => ⊤,
      fun _ x y _ _ => commute_of_hasNCommutingProperty_one hprop x y,
      fun g => ⟨0, Subgroup.mem_top g⟩⟩
  · -- h(1) ≥ 1 : `0` is not in the covering set, and the set is nonempty.
    rw [Nat.one_le_iff_ne_zero, Ne, Nat.sInf_eq_zero]
    push_neg
    refine ⟨fun hmem => ?_, ?_⟩
    · -- `0 ∈` set would cover `PUnit` by an empty family of subgroups — impossible.
      simp only [Set.mem_setOf_eq] at hmem
      obtain ⟨H, _, hcov⟩ := hmem PUnit commGroup_hasNCommutingProperty_one
      obtain ⟨i, _⟩ := hcov PUnit.unit
      exact i.elim0
    · -- `push_neg` left the goal as `.Nonempty`; `1` belongs to the set.
      refine ⟨1, ?_⟩
      intro G _ _ hprop
      exact ⟨fun _ => ⊤,
        fun _ x y _ _ => commute_of_hasNCommutingProperty_one hprop x y,
        fun g => ⟨0, Subgroup.mem_top g⟩⟩

/-- **`h(0) = 0`.** No group has the `0`-commuting property
    (`not_hasNCommutingProperty_zero`), so the covering hypothesis is false for
    every group and the implication defining the covering set is vacuously true —
    even for `k = 0`, whose empty family `Fin 0 → Subgroup G` would otherwise cover
    nothing. Hence `0` lies in the set and `h(0) = 0`. -/
theorem abelianCoverNumber_zero : abelianCoverNumber 0 = 0 := by
  unfold abelianCoverNumber
  apply Nat.le_zero.mp
  apply Nat.sInf_le
  intro G _ _ hprop
  exact absurd hprop not_hasNCommutingProperty_zero

/-- **`h(0) < h(1)`.** The covering number already increases at the base of the
    ladder: from `h(0) = 0` and `h(1) = 1`. (Pyber's exponential growth `c₁ⁿ <
    h(n) < c₂ⁿ` for large `n` remains unformalized.) -/
theorem abelianCoverNumber_zero_lt_one :
    abelianCoverNumber 0 < abelianCoverNumber 1 := by
  rw [abelianCoverNumber_zero, abelianCoverNumber_one]
  exact Nat.zero_lt_one

/- ## Structural theory of the `n`-commuting property

The covering *number* `h(n)` is bounded below only through Pyber's deep theorem
(the covering set is nonempty), but the underlying `n`-commuting *property* has a
clean, unconditional elementary theory: it is inherited by embeddings (hence by
subgroups), invariant under isomorphism, and eventually universal (every finite
group has it once the threshold reaches its order).  These are the closure
properties that make `HasNCommutingProperty` a genuine group-theoretic invariant,
all axiom-free. -/

/-- **The `n`-commuting property transfers along injective homomorphisms.** If
    `f : G →* H` is injective and `H` has the `n`-commuting property, then so does
    `G`: an `n`-exceeding subset `S ⊆ G` maps to an equal-cardinality subset
    `f(S) ⊆ H` (injectivity preserves cardinality), whose guaranteed distinct
    commuting pair `f a, f b` pulls back — `f (a*b) = f (b*a)` gives `a*b = b*a`,
    and `f a ≠ f b` gives `a ≠ b`.  So the property only ever *weakens* under
    embedding into a larger group. -/
theorem hasNCommutingProperty_of_injective {G H : Type*} [Group G] [Group H]
    {n : ℕ} (f : G →* H) (hf : Function.Injective f)
    (hH : HasNCommutingProperty H n) : HasNCommutingProperty G n := by
  classical
  intro S hS
  have hcard : (S.image f).card = S.card := Finset.card_image_of_injective S hf
  obtain ⟨x, y, hx, hy, hxy, hcomm⟩ := hH (S.image f) (by rw [hcard]; exact hS)
  rw [Finset.mem_image] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  refine ⟨a, b, ha, hb, fun hab => hxy (by rw [hab]), hf ?_⟩
  rw [map_mul, map_mul, hcomm]

/-- **Subgroups inherit the `n`-commuting property.** For any subgroup `K ≤ G`, if
    `G` has the `n`-commuting property then so does `K`, since the inclusion
    `K ↪ G` is an injective homomorphism (`hasNCommutingProperty_of_injective`).
    The property is therefore *hereditary*. -/
theorem hasNCommutingProperty_subgroup {G : Type*} [Group G] (K : Subgroup G)
    {n : ℕ} (h : HasNCommutingProperty G n) : HasNCommutingProperty K n :=
  hasNCommutingProperty_of_injective K.subtype K.subtype_injective h

/-- **The `n`-commuting property is an isomorphism invariant.** A group
    isomorphism `e : G ≃* H` carries the property from `G` to `H`, via the
    injective homomorphism `e.symm : H →* G` (`hasNCommutingProperty_of_injective`).
    Together with `hasNCommutingProperty_subgroup` this makes
    `HasNCommutingProperty` a genuine invariant of the isomorphism type. -/
theorem hasNCommutingProperty_of_mulEquiv {G H : Type*} [Group G] [Group H]
    {n : ℕ} (e : G ≃* H) (h : HasNCommutingProperty G n) :
    HasNCommutingProperty H n :=
  hasNCommutingProperty_of_injective e.symm.toMonoidHom e.symm.injective h

/-- **Every finite group has the `n`-commuting property once `n` reaches its
    order.** If `Fintype.card G ≤ n` then no subset of `G` can exceed size `n`
    (`Finset.card_le_univ`), so the defining condition is vacuously satisfied.
    Hence the property is *eventually universal*: for each finite `G` it holds for
    all large `n` — the elementary reason the interesting content of `h(n)` lives
    at thresholds below the group order. -/
theorem hasNCommutingProperty_of_card_le {G : Type*} [Group G] [Fintype G] {n : ℕ}
    (h : Fintype.card G ≤ n) : HasNCommutingProperty G n := by
  intro S hS
  have hSn : S.card ≤ n := (Finset.card_le_univ S).trans h
  exact absurd hS (Nat.not_lt.mpr hSn)
