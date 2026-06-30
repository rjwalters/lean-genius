/-
# Cantor Diagonalization OQ-06: the reals are uncountable

## Open Question
Formalize `¬ Countable ℝ` (equivalently: there is no surjection `ℕ → ℝ`), via Mathlib's
`Cardinal.not_countable_real`, or by transporting Cantor's theorem through
`Cardinal.mk_real`.

## Approach
Cantor's 1874 diagonal argument shows the reals cannot be enumerated. Mathlib packages
this as `Cardinal.not_countable_real : ¬ (Set.univ : Set ℝ).Countable` (proved via the
binary-expansion injection `{0,1}^ℕ ↪ ℝ`, so `#ℝ = 𝔠 = 2^ℵ₀ > ℵ₀`). This entry lifts it
to the type-level statement `¬ Countable ℝ`, derives the concrete "no surjection from ℕ"
form, and records the continuum cardinality `#ℝ = 𝔠` together with `ℵ₀ < #ℝ`.

Sorry-free and axiom-free.
-/
import Mathlib

namespace CantorDiagonalizationOQ06

open Cardinal

/-- The universal set of reals is not countable (Mathlib's `Cardinal.not_countable_real`). -/
theorem not_countable_univ_real : ¬ (Set.univ : Set ℝ).Countable :=
  Cardinal.not_countable_real

/-- **The reals are uncountable**, as a statement about the type `ℝ`:
there is no countable enumeration of `ℝ`. -/
theorem not_countable_real : ¬ Countable ℝ :=
  fun h => Cardinal.not_countable_real (Set.countable_univ_iff.mpr h)

/-- The reals carry the `Uncountable` typeclass. -/
theorem uncountable_real : Uncountable ℝ :=
  Set.not_countable_univ_iff.mp Cardinal.not_countable_real

/-- **No surjection `ℕ → ℝ`.** Cantor's theorem in its enumeration form: the reals cannot
be listed by the naturals.  A surjection from the (countable) naturals would make `ℝ`
countable, contradicting `not_countable_real`. -/
theorem not_surjective_nat_real (f : ℕ → ℝ) : ¬ Function.Surjective f :=
  fun hf => not_countable_real hf.countable

/-- The reals have cardinality the continuum, `#ℝ = 𝔠` (Mathlib's `Cardinal.mk_real`). -/
theorem mk_real_eq_continuum : #ℝ = 𝔠 :=
  Cardinal.mk_real

/-- `ℵ₀ < #ℝ`: the reals are strictly larger than the naturals — the quantitative form of
uncountability. -/
theorem aleph0_lt_mk_real : ℵ₀ < #ℝ := by
  rw [mk_real_eq_continuum]; exact aleph0_lt_continuum

end CantorDiagonalizationOQ06
