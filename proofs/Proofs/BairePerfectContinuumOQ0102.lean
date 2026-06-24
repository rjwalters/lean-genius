/-
  A complete metric space with no isolated points has cardinality at least the
  continuum.

  Open question OQ-01-OQ-02 (parent: baire-category-theorem, via OQ-01).

  The Baire-category entry derives the *uncountability* of a nonempty complete
  metric space without isolated points (a perfect Polish-type space): such a
  space cannot be written as a countable union of its singletons, since each
  singleton is nowhere dense. This file **sharpens uncountability to an explicit
  cardinal lower bound**: the space has cardinality at least `𝔠 = 2^ℵ₀`, the
  cardinality of the continuum.

  The mechanism is the classical **Cantor scheme**: in a perfect set inside a
  complete metric space one builds a binary tree of shrinking nonempty closed
  sets indexed by finite binary strings, and the intersection along each branch
  selects a distinct point. This yields a (continuous) injection

      (ℕ → Bool)  ↪  C,

  and since `#(ℕ → Bool) = 2^ℵ₀ = 𝔠`, the perfect set — hence the whole space —
  has at least `𝔠` points. Mathlib packages the tree construction as
  `Perfect.exists_nat_bool_injection`; this file assembles it into the cardinal
  statement, which Mathlib does not record on its own.

  ## Contents

  * `mk_nat_arrow_bool` — the cardinal arithmetic `#(ℕ → Bool) = 𝔠`.
  * `continuum_le_mk_of_perfect` — the headline: a nonempty perfect set in a
    complete metric space has cardinality `≥ 𝔠`.
  * `continuum_le_mk_of_perfectSpace` — the space-level form: a nonempty complete
    metric space with no isolated points (`PerfectSpace`) has `𝔠 ≤ #α`.
  * `aleph0_lt_mk_of_perfectSpace` / `not_countable_of_perfectSpace` — recovering
    (and strictly sharpening) uncountability as a corollary.
  * `perfectSpace_iff_no_isolated` — bridge confirming `PerfectSpace` is exactly
    the "no isolated points" hypothesis of the open question.
  * `continuum_le_mk_real` — the motivating instance: `𝔠 ≤ #ℝ`, since `ℝ` is a
    nontrivial connected complete metric space.

  Everything is verified: no `sorry`, no `axiom`, no `native_decide`.
-/
import Mathlib

namespace BairePerfectContinuum

open Cardinal Set

/-- The cardinal arithmetic underlying the bound: the set of binary sequences has
the cardinality of the continuum, `#(ℕ → Bool) = 2^ℵ₀ = 𝔠`. -/
theorem mk_nat_arrow_bool : #(ℕ → Bool) = 𝔠 := by
  rw [mk_arrow, mk_bool, mk_nat, lift_two, lift_aleph0, two_power_aleph0]

/-- **A nonempty perfect set in a complete metric space has cardinality at least
the continuum.** The Cantor-scheme injection `(ℕ → Bool) ↪ C`
(`Perfect.exists_nat_bool_injection`) corestricts to `C`, so
`𝔠 = #(ℕ → Bool) ≤ #C`. -/
theorem continuum_le_mk_of_perfect {α : Type} [MetricSpace α] [CompleteSpace α]
    {C : Set α} (hC : Perfect C) (hne : C.Nonempty) : 𝔠 ≤ #C := by
  obtain ⟨f, hrange, _hcont, hf⟩ := hC.exists_nat_bool_injection hne
  -- corestrict the injection to land in `C`
  have hmem : ∀ x, f x ∈ C := fun x => hrange (mem_range_self x)
  have hg : Function.Injective (fun x : ℕ → Bool => (⟨f x, hmem x⟩ : C)) :=
    fun a b hab => hf (Subtype.ext_iff.mp hab)
  calc 𝔠 = #(ℕ → Bool) := mk_nat_arrow_bool.symm
    _ ≤ #C := mk_le_of_injective hg

/-- **A nonempty complete metric space with no isolated points has cardinality at
least the continuum.** `PerfectSpace α` says the whole space is a perfect set;
applying `continuum_le_mk_of_perfect` to `univ` and rewriting `#(univ) = #α`
gives `𝔠 ≤ #α`. This is the open question's statement. -/
theorem continuum_le_mk_of_perfectSpace {α : Type} [MetricSpace α] [CompleteSpace α]
    [PerfectSpace α] [Nonempty α] : 𝔠 ≤ #α := by
  have hp : Perfect (Set.univ : Set α) := @PerfectSpace.univ_perfect α _ _
  have h := continuum_le_mk_of_perfect (α := α) hp univ_nonempty
  rwa [mk_univ] at h

/-- **Sharpened uncountability.** A nonempty complete metric space with no
isolated points has strictly more than `ℵ₀` points (`ℵ₀ < #α`): the continuum is
itself uncountable (`ℵ₀ < 𝔠`) and bounds `#α` from below. This strictly improves
the bare "uncountable" statement of the parent entry. -/
theorem aleph0_lt_mk_of_perfectSpace {α : Type} [MetricSpace α] [CompleteSpace α]
    [PerfectSpace α] [Nonempty α] : ℵ₀ < #α :=
  aleph0_lt_continuum.trans_le continuum_le_mk_of_perfectSpace

/-- A nonempty complete metric space with no isolated points is uncountable as a
type. -/
theorem not_countable_of_perfectSpace {α : Type} [MetricSpace α] [CompleteSpace α]
    [PerfectSpace α] [Nonempty α] : ¬ Countable α := by
  rw [← mk_le_aleph0_iff, not_le]
  exact aleph0_lt_mk_of_perfectSpace

/-- Bridge: `PerfectSpace α` is exactly the "no isolated points" hypothesis —
every point is an accumulation point of its complement, i.e. the punctured
neighbourhood filter `𝓝[≠] x` is nontrivial for all `x`. -/
theorem perfectSpace_iff_no_isolated {α : Type} [TopologicalSpace α] :
    PerfectSpace α ↔ ∀ x : α, (nhdsWithin x {x}ᶜ).NeBot :=
  perfectSpace_iff_forall_not_isolated

/-- **Motivating instance: `𝔠 ≤ #ℝ`.** The real line is a nontrivial connected
`T1` complete metric space, hence a `PerfectSpace`, so the general bound applies.
(In fact `#ℝ = 𝔠`; the point here is that the cardinality floor falls out of the
purely topological "no isolated points" hypothesis.) -/
theorem continuum_le_mk_real : 𝔠 ≤ #ℝ :=
  continuum_le_mk_of_perfectSpace

end BairePerfectContinuum
