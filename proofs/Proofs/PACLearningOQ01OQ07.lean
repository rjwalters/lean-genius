/-
  PAC Learning OQ-01 OQ-07: VC Dimension of Thresholds over an Arbitrary Linear Order

  Generalizes `PACLearningOQ01` (thresholds on ℕ have VC dimension 1) to thresholds
  on ANY totally ordered set `[LinearOrder α]`. The parent proof for ℕ used arithmetic
  (`a + 1`, `Nat.not_lt_zero`, `omega`); here we use ONLY the order axioms.

  Two phenomena replace the ℕ-specific arithmetic:

  - Part II (lower bound). Over ℕ every singleton `{a}` is shattered, because every `a`
    has a successor `a + 1`. Over a general linear order this is FALSE at a maximum:
    a top element cannot be included by any threshold `{x | x < t}`. The honest
    statement is the sharp characterisation
        `Shatters thresholds {a} ↔ ∃ b, a < b`   (i.e. `a` is not a maximum).
    Hence VC dim ≥ 1 precisely when the order is `Nontrivial`.

  - Part III (upper bound). No 2-element set is shattered — this holds over EVERY linear
    order with no extra hypothesis, by the same monotonicity obstruction as the parent,
    but discharged with `lt_of_lt_of_le` / `lt_asymm` instead of `omega`.

  Vapnik-Chervonenkis (1971).
-/
import Mathlib

namespace LearningTheory.VCDimension.LinearOrderThresholds

open Finset

variable {α : Type*} [LinearOrder α]

/-- A hypothesis class `H ⊆ Set α` shatters a finite set `S ⊆ α` if every subset
    `T ⊆ S` is realised as `h ∩ S` for some `h ∈ H`. Identical to the parent's
    `Shatters`, now over an arbitrary type. -/
def Shatters (H : Set (Set α)) (S : Finset α) : Prop :=
  ∀ T : Finset α, T ⊆ S → ∃ h ∈ H, ∀ x ∈ S, (x ∈ h ↔ x ∈ T)

/-- Threshold classifiers on a linear order: `h_t = { x | x < t }` for `t : α`. -/
def thresholdClassifiers : Set (Set α) :=
  { h | ∃ t : α, h = { x | x < t } }

/-! ## Part II — Lower bound: which singletons are shattered

The defining feature of the general case: a singleton `{a}` is shattered exactly when
`a` is not a maximum of the order. -/

/-- **Sharp characterisation.** Thresholds shatter the singleton `{a}` if and only if
    `a` has a strict upper bound. Forward: to realise the labelling `T = {a}` we need a
    threshold including `a`, i.e. some `t` with `a < t`. Backward: such a `t` includes
    `a`, while `t = a` excludes it.

    Over ℕ the right side `∃ b, a < b` is always true (`b = a + 1`), recovering the
    parent's unconditional `threshold_shatters_singleton`. -/
theorem threshold_shatters_singleton_iff (a : α) :
    Shatters thresholdClassifiers ({a} : Finset α) ↔ ∃ b, a < b := by
  constructor
  · -- Shattering realises `T = {a}`, forcing a threshold above `a`.
    intro hShatter
    obtain ⟨h, ⟨t, ht⟩, hh⟩ := hShatter {a} (Finset.Subset.refl _)
    subst ht
    have ha_mem : a ∈ ({a} : Finset α) := Finset.mem_singleton_self a
    have hiff := hh a ha_mem
    -- `hiff : a ∈ {x | x < t} ↔ a ∈ {a}`, and `a ∈ {a}` holds.
    exact ⟨t, hiff.mpr ha_mem⟩
  · -- Build the two thresholds explicitly.
    rintro ⟨b, hab⟩
    intro T _
    by_cases ha : a ∈ T
    · -- Include `a`: threshold `b` works since `a < b`.
      refine ⟨{x | x < b}, ⟨b, rfl⟩, ?_⟩
      intro x hx
      rw [Finset.mem_singleton] at hx; subst hx
      exact ⟨fun _ => ha, fun _ => hab⟩
    · -- Exclude `a`: threshold `a` works since `¬ a < a`.
      refine ⟨{x | x < a}, ⟨a, rfl⟩, ?_⟩
      intro x hx
      rw [Finset.mem_singleton] at hx; subst hx
      exact ⟨fun h => absurd h (lt_irrefl _), fun h => absurd h ha⟩

/-- Every non-maximal element's singleton is shattered (the convenient direction). -/
theorem threshold_shatters_singleton {a b : α} (hab : a < b) :
    Shatters thresholdClassifiers ({a} : Finset α) :=
  (threshold_shatters_singleton_iff a).mpr ⟨b, hab⟩

/-! ## Part III — Upper bound: no pair is shattered (any linear order) -/

/-- Thresholds cannot shatter any 2-element set `{a, b}` with `a < b`. The labelling
    `T = {b}` (select only the larger point) demands a threshold `t` with `t ≤ a` (to
    exclude `a`) and `b < t` (to include `b`); then `b < t ≤ a` contradicts `a < b`.
    Pure order reasoning — no arithmetic. -/
theorem threshold_not_shatters_pair {a b : α} (hab : a < b) :
    ¬ Shatters thresholdClassifiers ({a, b} : Finset α) := by
  intro hShatter
  -- Witness labelling `T = {b}`.
  have hSub : ({b} : Finset α) ⊆ ({a, b} : Finset α) := by
    intro x hx
    rw [Finset.mem_singleton] at hx; subst hx; simp
  obtain ⟨h, ⟨t, ht⟩, hh⟩ := hShatter ({b} : Finset α) hSub
  subst ht
  have ha_mem : a ∈ ({a, b} : Finset α) := by simp
  have hb_mem : b ∈ ({a, b} : Finset α) := by simp
  have ha := hh a ha_mem  -- a < t ↔ a ∈ {b}
  have hb := hh b hb_mem  -- b < t ↔ b ∈ {b}
  -- `a` is excluded: `a ∉ {b}` because `a ≠ b`.
  have ha' : ¬ (a < t) := by
    intro hlt
    have hmem : a ∈ ({b} : Finset α) := ha.mp hlt
    rw [Finset.mem_singleton] at hmem
    exact absurd hmem (ne_of_lt hab)
  -- `b` is included.
  have hb' : b < t := hb.mpr (Finset.mem_singleton_self b)
  -- `b < t ≤ a` versus `a < b`.
  exact lt_asymm hab (lt_of_lt_of_le hb' (le_of_not_gt ha'))

/-! ## Combined bounds -/

/-- **VC dimension of thresholds over a linear order is exactly 1.**

    Upper bound (unconditional): no two-element set is shattered. Lower bound (needs the
    order to be `Nontrivial`, otherwise there is nothing to learn): some singleton is
    shattered. Over ℕ this recovers `threshold_vcdim_bounds`. -/
theorem threshold_vcdim_bounds [Nontrivial α] :
    (∃ a : α, Shatters thresholdClassifiers ({a} : Finset α)) ∧
    (∀ a b : α, a ≠ b → ¬ Shatters thresholdClassifiers ({a, b} : Finset α)) := by
  refine ⟨?_, ?_⟩
  · -- Nontriviality gives a strictly comparable pair; its smaller element is shattered.
    obtain ⟨a, b, hne⟩ := exists_pair_ne α
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨a, threshold_shatters_singleton hlt⟩
    · exact ⟨b, threshold_shatters_singleton hgt⟩
  · intro a b hab hShatter
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact threshold_not_shatters_pair hlt hShatter
    · -- `{a, b} = {b, a}`; reuse the pair lemma with arguments swapped.
      have heq : ({a, b} : Finset α) = ({b, a} : Finset α) := by
        ext x; simp [Or.comm]
      rw [heq] at hShatter
      exact threshold_not_shatters_pair hgt hShatter

end LearningTheory.VCDimension.LinearOrderThresholds
