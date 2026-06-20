/-
# Denumerability of the Rationals OQ-05: closure of ℵ₀ — and where it breaks

## Open Question
Pin down exactly which constructions preserve the denumerability of ℚ. Finite products,
finite subsets, and finite sequences of rationals are all still denumerable (cardinality
ℵ₀); but the *countably infinite* power `ℕ → ℚ` is not — it jumps to the continuum 𝔠.

## Approach
Everything rests on `#ℚ = ℵ₀` (`mk_eq_aleph0`, since ℚ is countable and infinite) together
with the absorption laws of `ℵ₀`:
  * `#(ℚ × ℚ) = ℵ₀`  via `mk_prod` and `aleph0_mul_aleph0 : ℵ₀ · ℵ₀ = ℵ₀`.
  * `#(List ℚ) = ℵ₀` via `mk_list_eq_aleph0` (finite sequences of a countable type).
  * `#(Finset ℚ) = ℵ₀` via `mk_finset_of_infinite` (finite subsets of an infinite type).
  * `#(ℕ → ℚ) = 𝔠`  via `mk_arrow` and `aleph0_power_aleph0 : ℵ₀ ^ ℵ₀ = 𝔠` — the
    countable power escapes ℵ₀.

The contrast is the point: ℵ₀ absorbs every *finite* operation but a countable *power*
already reaches the continuum. This is the ℵ₀-level shadow of the continuum results
(`𝔠 · 𝔠 = 𝔠`, `𝔠 ^ ℵ₀ = 𝔠`) and sharpens the gallery's `ℵ₀ < 𝔠` cardinality gap.

Sorry-free and axiom-free.
-/
import Mathlib

namespace DenumerabilityRationalsOQ05

open Cardinal

/-- **`#ℚ = ℵ₀`.** The rationals are denumerable: countable and infinite, hence exactly
`ℵ₀` (`Cardinal.mk_eq_aleph0`). This is the engine for everything below. -/
theorem mk_rat : #ℚ = ℵ₀ :=
  mk_eq_aleph0 ℚ

/-- **`#(ℚ × ℚ) = ℵ₀`.** Pairs of rationals are still denumerable: `mk_prod` gives
`#ℚ · #ℚ`, and `aleph0_mul_aleph0` collapses `ℵ₀ · ℵ₀` to `ℵ₀`. The ℵ₀-analogue of OQ-07's
`𝔠 · 𝔠 = 𝔠`. -/
theorem mk_rat_prod : #(ℚ × ℚ) = ℵ₀ := by
  rw [mk_prod, lift_id, mk_rat, aleph0_mul_aleph0]

/-- **The plane of rationals equals the line of rationals: `#(ℚ × ℚ) = #ℚ`.** Both are
`ℵ₀`. -/
theorem mk_rat_prod_eq_mk_rat : #(ℚ × ℚ) = #ℚ := by
  rw [mk_rat_prod, mk_rat]

/-- **An explicit bijection `ℚ × ℚ ≃ ℚ` exists** (`Cardinal.eq`). -/
theorem nonempty_equiv_prod_rat : Nonempty (ℚ × ℚ ≃ ℚ) :=
  Cardinal.eq.mp mk_rat_prod_eq_mk_rat

/-- **`#(List ℚ) = ℵ₀`.** Finite sequences of rationals are denumerable
(`mk_list_eq_aleph0`, valid for any countable nonempty type). -/
theorem mk_list_rat : #(List ℚ) = ℵ₀ :=
  mk_list_eq_aleph0 ℚ

/-- **`#(Finset ℚ) = ℵ₀`.** Finite subsets of ℚ are denumerable: `mk_finset_of_infinite`
gives `#(Finset ℚ) = #ℚ`, and `mk_rat` rewrites it to `ℵ₀`. -/
theorem mk_finset_rat : #(Finset ℚ) = ℵ₀ := by
  rw [mk_finset_of_infinite, mk_rat]

/-- **The boundary: `#(ℕ → ℚ) = 𝔠`.** Where finite operations keep ℚ at `ℵ₀`, the
*countable power* of rational sequences already reaches the continuum: `mk_arrow` gives
`#ℚ ^ #ℕ = ℵ₀ ^ ℵ₀`, collapsed by `aleph0_power_aleph0` to `𝔠`. So `ℕ → ℚ` is *uncountable*,
equinumerous with ℝ — the sharp companion to the rest of this file. -/
theorem mk_seq_rat : #(ℕ → ℚ) = 𝔠 := by
  rw [mk_arrow, lift_uzero, lift_uzero, mk_rat, mk_nat, aleph0_power_aleph0]

/-- **`ℕ → ℚ` is uncountable.** Immediate from `mk_seq_rat` and `aleph0_lt_continuum`
(`ℵ₀ < 𝔠`): rational sequences are strictly more numerous than the rationals themselves. -/
theorem not_countable_seq_rat : ¬ Countable (ℕ → ℚ) := by
  rw [← mk_le_aleph0_iff, mk_seq_rat, not_le]
  exact aleph0_lt_continuum

end DenumerabilityRationalsOQ05
