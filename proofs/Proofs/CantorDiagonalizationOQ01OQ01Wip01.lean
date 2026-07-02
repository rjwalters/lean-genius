/-
# Intermediate cardinals: complete structural characterization (OQ-01-OQ-01-WIP-01)

## Parent question

The gallery entry `cantor-diagonalization-oq-01-oq-01` ("The Continuum Hypothesis:
Independence and Consequences") answers the question

  *Does there exist a cardinal κ with ℵ₀ < κ < 2^ℵ₀?*

by proving `intermediate_iff_not_ch`: **an intermediate cardinal exists iff CH fails.**
It also exhibits ℵ₁ as *an* intermediate under ¬CH, and states König's constraint on
the possible values of 2^ℵ₀.

## What this file adds

The parent settles *existence*. It leaves open the finer, purely ZFC-provable
**structural** question: *which* cardinals are the intermediates, and is there a least
one? This file gives the complete answer, axiom-free, directly from Mathlib's
`Cardinal.aleph` API:

* `intermediate_is_aleph`         — every intermediate cardinal is `ℵ_ o` for some `0 < o`
  (there are no "exotic" intermediates outside the aleph hierarchy).
* `aleph_one_le_of_intermediate`  — **ℵ₁ is a lower bound**: every intermediate `κ` has `ℵ₁ ≤ κ`.
* `aleph_one_intermediate_iff_not_ch` — ℵ₁ *is* intermediate exactly when CH fails.
* `least_intermediate`            — whenever an intermediate exists, **ℵ₁ is the least one**
  (it is intermediate and bounds all intermediates below).
* `intermediate_iff`              — the exact membership test:
  `κ` is intermediate ↔ `κ = ℵ_ o` with `0 < o` and `ℵ_ o < 𝔠`.
* `intermediate_iff_lt_index`     — writing `𝔠 = ℵ_ δ` (the continuum is always an aleph),
  the intermediates are **exactly** `{ ℵ_ o : 0 < o < δ }` — a bijection with the ordinal
  interval `(0, δ)`. This pins down the whole set, not just whether it is nonempty.

So beyond "an intermediate exists ⟺ ¬CH", the intermediate cardinals form an initial
segment of the uncountable alephs with least element ℵ₁, indexed by the ordinals strictly
between `0` and the aleph-index of the continuum.

`CH` is taken here as `𝔠 = ℵ₁` (definitionally the same as
`Proofs.ContinuumHypothesis.CH`, which unfolds to `2 ^ ℵ₀ = aleph 1`); we work with
Mathlib's `𝔠` throughout and `two_power_aleph0 : 2 ^ ℵ₀ = 𝔠` bridges the two.

## References
- Kanamori, A. (2003). *The Higher Infinite*, §1 (the aleph hierarchy).
- Jech, T. (2003). *Set Theory*, ch. 3 (cardinal arithmetic, König).
-/

import Mathlib

namespace CantorDiagOQ0101Wip01

open Cardinal Ordinal

/-- A cardinal is **intermediate** if it lies strictly between `ℵ₀` and the continuum
`𝔠 = 2 ^ ℵ₀`. -/
def Intermediate (κ : Cardinal.{0}) : Prop := ℵ₀ < κ ∧ κ < 𝔠

/-- The Continuum Hypothesis, stated as `𝔠 = ℵ₁`. This unfolds to `2 ^ ℵ₀ = aleph 1`
via `two_power_aleph0`, matching `Proofs.ContinuumHypothesis.CH`. -/
def CH : Prop := (𝔠 : Cardinal.{0}) = ℵ₁

/-! ## Basic reformulations -/

/-- `ℵ₁ ≤ 𝔠` always holds in ZFC (this is just `Cardinal.aleph_one_le_continuum`). -/
theorem aleph_one_le_continuum : (ℵ₁ : Cardinal.{0}) ≤ 𝔠 := Cardinal.aleph_one_le_continuum

/-- CH is equivalent to `ℵ₁` being *not* strictly below the continuum. -/
theorem ch_iff_not_aleph_one_lt : CH ↔ ¬ (ℵ₁ : Cardinal.{0}) < 𝔠 := by
  unfold CH
  constructor
  · intro h; rw [h]; exact lt_irrefl _
  · intro h
    exact le_antisymm (not_lt.mp h) aleph_one_le_continuum

/-- `¬CH` is equivalent to `ℵ₁ < 𝔠`: the continuum genuinely overshoots ℵ₁. -/
theorem not_ch_iff_aleph_one_lt : ¬CH ↔ (ℵ₁ : Cardinal.{0}) < 𝔠 := by
  rw [ch_iff_not_aleph_one_lt, not_not]

/-! ## Every intermediate cardinal is an uncountable aleph -/

/-- **No exotic intermediates.** Any intermediate cardinal is `ℵ_ o` for some ordinal
`o > 0`. This is because every cardinal `≥ ℵ₀` is an aleph, and being `> ℵ₀ = ℵ_ 0`
forces a positive index. -/
theorem intermediate_is_aleph {κ : Cardinal.{0}} (h : Intermediate κ) :
    ∃ o : Ordinal.{0}, 0 < o ∧ κ = ℵ_ o := by
  obtain ⟨hlo, _⟩ := h
  -- κ ≥ ℵ₀, hence κ = ℵ_ o for some o.
  obtain ⟨o, ho⟩ := mem_range_aleph_iff.mpr (le_of_lt hlo)
  refine ⟨o, ?_, ho.symm⟩
  -- ℵ_ 0 = ℵ₀ < κ = ℵ_ o forces 0 < o.
  have : ℵ_ (0 : Ordinal.{0}) < ℵ_ o := by
    rw [aleph_zero, ho]; exact hlo
  exact aleph_lt_aleph.mp this

/-- **ℵ₁ is a lower bound for the intermediates.** Every intermediate cardinal is `≥ ℵ₁`,
so there is no room strictly between `ℵ₀` and `ℵ₁`. -/
theorem aleph_one_le_of_intermediate {κ : Cardinal.{0}} (h : Intermediate κ) : ℵ₁ ≤ κ := by
  obtain ⟨o, hpos, hko⟩ := intermediate_is_aleph h
  rw [hko]
  -- 0 < o gives 1 ≤ o, hence ℵ_ 1 ≤ ℵ_ o.
  exact aleph_le_aleph.mpr (Ordinal.one_le_iff_ne_zero.mpr hpos.ne')

/-! ## ℵ₁ as the least intermediate -/

/-- `ℵ₁` is intermediate exactly when CH fails. Combined with `aleph_one_le_of_intermediate`
this says ℵ₁ is the *canonical smallest candidate*. -/
theorem aleph_one_intermediate_iff_not_ch : Intermediate (ℵ₁) ↔ ¬CH := by
  rw [not_ch_iff_aleph_one_lt]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨aleph0_lt_aleph_one, h⟩

/-- **An intermediate cardinal exists iff CH fails.** (Reproves the parent's headline
equivalence from the structural lemmas.) -/
theorem exists_intermediate_iff_not_ch : (∃ κ, Intermediate κ) ↔ ¬CH := by
  constructor
  · rintro ⟨κ, hκ⟩ hch
    -- Under CH, ℵ₁ ≤ κ < 𝔠 = ℵ₁ is contradictory.
    have h1 : ℵ₁ ≤ κ := aleph_one_le_of_intermediate hκ
    have h2 : κ < 𝔠 := hκ.2
    rw [(show 𝔠 = ℵ₁ from hch)] at h2
    exact absurd (h1.trans_lt h2) (lt_irrefl _)
  · intro h
    exact ⟨ℵ₁, aleph_one_intermediate_iff_not_ch.mpr h⟩

/-- **ℵ₁ is the least intermediate.** Whenever any intermediate cardinal exists, `ℵ₁`
is itself intermediate and is a lower bound for every intermediate cardinal — i.e. it is
the minimum of the intermediate set. -/
theorem least_intermediate (h : ∃ κ, Intermediate κ) :
    Intermediate (ℵ₁) ∧ ∀ κ, Intermediate κ → ℵ₁ ≤ κ := by
  have hnc : ¬CH := exists_intermediate_iff_not_ch.mp h
  exact ⟨aleph_one_intermediate_iff_not_ch.mpr hnc, fun _ hκ => aleph_one_le_of_intermediate hκ⟩

/-! ## Exact characterization of the intermediate set -/

/-- **Membership test.** A cardinal is intermediate iff it is `ℵ_ o` for a positive
ordinal `o` whose aleph is still below the continuum. -/
theorem intermediate_iff {κ : Cardinal.{0}} :
    Intermediate κ ↔ ∃ o : Ordinal.{0}, 0 < o ∧ κ = ℵ_ o ∧ ℵ_ o < 𝔠 := by
  constructor
  · intro h
    obtain ⟨o, hpos, hko⟩ := intermediate_is_aleph h
    exact ⟨o, hpos, hko, hko ▸ h.2⟩
  · rintro ⟨o, hpos, hko, hlt⟩
    refine ⟨?_, ?_⟩
    · -- ℵ₀ = ℵ_ 0 < ℵ_ o = κ since 0 < o.
      rw [hko, ← aleph_zero]
      exact aleph_lt_aleph.mpr hpos
    · rw [hko]; exact hlt

/-- The continuum is itself an aleph: `𝔠 = ℵ_ δ` for some ordinal `δ` (indeed `δ ≥ 1`). -/
theorem exists_continuum_index : ∃ δ : Ordinal.{0}, 𝔠 = ℵ_ δ := by
  obtain ⟨δ, hδ⟩ := mem_range_aleph_iff.mpr (le_of_lt aleph0_lt_continuum)
  exact ⟨δ, hδ.symm⟩

/-- **The intermediate set, pinned down.** Fixing the aleph-index `δ` of the continuum
(`𝔠 = ℵ_ δ`), the intermediate cardinals are *exactly* the alephs `ℵ_ o` for `0 < o < δ`.
Thus the intermediates are order-isomorphic (via `o ↦ ℵ_ o`) to the ordinal interval
`(0, δ)`, and their number is entirely determined by where the continuum sits in the
aleph hierarchy. -/
theorem intermediate_iff_lt_index {δ : Ordinal.{0}} (hδ : 𝔠 = ℵ_ δ) {κ : Cardinal.{0}} :
    Intermediate κ ↔ ∃ o : Ordinal.{0}, 0 < o ∧ o < δ ∧ κ = ℵ_ o := by
  rw [intermediate_iff]
  constructor
  · rintro ⟨o, hpos, hko, hlt⟩
    rw [hδ] at hlt
    exact ⟨o, hpos, aleph_lt_aleph.mp hlt, hko⟩
  · rintro ⟨o, hpos, hlt, hko⟩
    refine ⟨o, hpos, hko, ?_⟩
    rw [hδ]
    exact aleph_lt_aleph.mpr hlt

/-- Corollary: under ¬CH the least intermediate is ℵ₁, and the intermediates are the
alephs `ℵ_ o` with `1 ≤ o < δ` (where `𝔠 = ℵ_ δ`), so `δ ≥ 2`. -/
theorem not_ch_index_ge_two {δ : Ordinal.{0}} (hδ : 𝔠 = ℵ_ δ) (h : ¬CH) : 2 ≤ δ := by
  have hlt : ℵ₁ < 𝔠 := not_ch_iff_aleph_one_lt.mp h
  rw [hδ] at hlt
  have h1 : (1 : Ordinal.{0}) < δ := aleph_lt_aleph.mp hlt
  -- 1 < δ means 2 = succ 1 ≤ δ.
  have h2 : (2 : Ordinal.{0}) = Order.succ (1 : Ordinal.{0}) := by
    rw [Order.succ_eq_add_one, one_add_one_eq_two]
  rw [h2]
  exact Order.succ_le_of_lt h1

end CantorDiagOQ0101Wip01
