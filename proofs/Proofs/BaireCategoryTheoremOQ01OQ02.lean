import Mathlib

/-!
# Continuum-cardinality lower bound for perfect complete metric spaces

This file sharpens the *uncountability* of a nonempty perfect complete metric space
(the classical Baire-category consequence) to an exact **cardinality** statement:

> A nonempty perfect set in a complete metric space has cardinality **at least the
> continuum** `𝔠`.  In particular a complete metric space **with no isolated points**
> (a `PerfectSpace`) that is nonempty has `𝔠 ≤ #X`.

This answers the open question attached to the gallery Baire proof
(`baire-category-theorem-oq-01-oq-02`): *"Show that a complete metric space with no
isolated points has cardinality at least that of the continuum, sharpening the
uncountability of `ℝ` obtained here."*

## The argument

The heavy lifting is the **Cantor scheme** embedding already in Mathlib,
`Perfect.exists_nat_bool_injection`: a nonempty perfect set `C` in a complete metric
space admits a (continuous) **injection** `f : (ℕ → Bool) → α` with `range f ⊆ C`.
Corestricting `f` to the subtype `C` gives an injection `(ℕ → Bool) ↪ C`, hence
`#(ℕ → Bool) ≤ #C`.  Since `#(ℕ → Bool) = 2 ^ ℵ₀ = 𝔠`, the continuum bound follows.
(The corestriction is routed through `ULift` to keep the source and target in the same
universe for the cardinal comparison.)

Mathlib stops at the injection; it has no statement that a perfect set, or a
`PerfectSpace`, has at least continuum-many points.  The cardinal corollary assembled
here is the genuinely new content.

## Main results

* `Cardinal.mk_nat_arrow_bool` — `#(ℕ → Bool) = 𝔠` (a reusable cardinal computation).
* `Perfect.continuum_le_mk` — `𝔠 ≤ #C` for a nonempty perfect set `C` in a complete
  metric space.
* `Perfect.not_countable` — such a `C` is uncountable (recovering and refining the
  Baire conclusion).
* `PerfectSpace.continuum_le_mk` — `𝔠 ≤ #α` for a nonempty complete metric space with
  no isolated points.  This is the headline statement of the open question.
* `PerfectSpace.uncountable` — such a space is uncountable.

All results are fully machine-checked, no `sorry`, no extra axioms.
-/

open Cardinal Set Function

namespace BaireContinuumOQ01OQ02

universe u

/-- The Cantor space `ℕ → Bool` has cardinality exactly the continuum,
`#(ℕ → Bool) = 𝔠`.  Reusable cardinal computation underlying the bound below. -/
theorem Cardinal.mk_nat_arrow_bool : #(ℕ → Bool) = 𝔠 := by
  rw [Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat]
  simp only [Cardinal.lift_id]
  exact Cardinal.two_power_aleph0

variable {α : Type u} [MetricSpace α] [CompleteSpace α]

/-- **Continuum lower bound for perfect sets.**  A nonempty perfect set `C` in a
complete metric space has at least continuum-many points: `𝔠 ≤ #C`.

The proof corestricts Mathlib's Cantor-scheme injection
`Perfect.exists_nat_bool_injection` to the subtype `C` (via `ULift` to match
universes), then computes `#(ℕ → Bool) = 𝔠`. -/
theorem Perfect.continuum_le_mk {C : Set α} (hC : Perfect C) (hne : C.Nonempty) :
    𝔠 ≤ #C := by
  obtain ⟨f, hrange, _, hinj⟩ := hC.exists_nat_bool_injection hne
  -- corestrict `f` to land in the subtype `C`, with source lifted to universe `u`
  have hginj : Injective
      (fun x : ULift.{u} (ℕ → Bool) => (⟨f x.down, hrange (mem_range_self x.down)⟩ : C)) := by
    intro a b hab
    exact ULift.down_injective (hinj (congrArg Subtype.val hab))
  have hle : #(ULift.{u} (ℕ → Bool)) ≤ #C := Cardinal.mk_le_of_injective hginj
  rwa [Cardinal.mk_uLift, Cardinal.mk_nat_arrow_bool, Cardinal.lift_continuum] at hle

/-- A nonempty perfect set in a complete metric space is uncountable.  This recovers
the Baire-category conclusion (`ℝ` is uncountable) and is strictly weaker than the
continuum bound `Perfect.continuum_le_mk`. -/
theorem Perfect.not_countable {C : Set α} (hC : Perfect C) (hne : C.Nonempty) :
    ¬ C.Countable := by
  intro h
  have h1 : 𝔠 ≤ #C := Perfect.continuum_le_mk hC hne
  have h2 : #C ≤ ℵ₀ := Cardinal.le_aleph0_iff_set_countable.2 h
  exact absurd (h1.trans h2) (not_le.2 Cardinal.aleph0_lt_continuum)

variable (α) in
/-- **Continuum lower bound for a perfect space.**  A nonempty complete metric space
with no isolated points (a `PerfectSpace`) has at least continuum-many points:
`𝔠 ≤ #α`.

This is the headline statement of the open question: a complete metric space with no
isolated points has cardinality at least that of the continuum, sharpening the bare
uncountability obtained from Baire's theorem. -/
theorem PerfectSpace.continuum_le_mk [PerfectSpace α] [Nonempty α] : 𝔠 ≤ #α := by
  have huniv : Perfect (Set.univ : Set α) := PerfectSpace.univ_perfect (α := α)
  have hbound : 𝔠 ≤ #(Set.univ : Set α) := Perfect.continuum_le_mk huniv Set.univ_nonempty
  rwa [Cardinal.mk_univ] at hbound

variable (α) in
/-- A nonempty complete metric space with no isolated points is uncountable. -/
theorem PerfectSpace.uncountable [PerfectSpace α] [Nonempty α] : Uncountable α :=
  Cardinal.aleph0_lt_mk_iff.1 (Cardinal.aleph0_lt_continuum.trans_le (PerfectSpace.continuum_le_mk α))

end BaireContinuumOQ01OQ02
