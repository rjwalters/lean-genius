/-
# Cantor Diagonalization OQ-05: the continuum is stable under countable powers, #(ℕ → ℝ) = #ℝ

## Open Question
Formalize `#(ℕ → ℝ) = #ℝ` (equivalently `𝔠 ^ ℵ₀ = 𝔠`): the space of *real
sequences* has the same cardinality as the real line, via Mathlib's `Cardinal.mk_arrow`,
`Cardinal.mk_real`, `Cardinal.mk_nat`, and the countable-power theorem
`Cardinal.continuum_power_aleph0`.

## Approach
This is the countable-power strengthening of OQ-07. Where OQ-07 shows the *finite*
product `#(ℝ × ℝ) = 𝔠` (doubling the dimension does not raise cardinality), the present
companion shows the continuum is stable even under a *countably infinite* power: passing
from `ℝ` to the whole sequence space `ℕ → ℝ` still does not increase cardinality.

`Cardinal.mk_arrow` expands `#(ℕ → ℝ)` to `#ℝ ^ #ℕ`; `Cardinal.mk_real` and
`Cardinal.mk_nat` rewrite the base and exponent to `𝔠` and `ℵ₀`; and
`Cardinal.continuum_power_aleph0 : 𝔠 ^ ℵ₀ = 𝔠` collapses the power. The cardinal equality
then unpacks, via `Cardinal.eq`, to an honest bijection `(ℕ → ℝ) ≃ ℝ`.

The same engine yields Baire space `#(ℕ → ℕ) = 𝔠` (`aleph0_power_aleph0`) and, in full
generality, `#(ℕ → α) = 𝔠` for every type `α` sandwiched `2 ≤ #α ≤ 𝔠`
(`power_aleph0_of_le_continuum`). Since a countable power dominates any finite product,
this subsumes OQ-07: both the plane `ℝ × ℝ` and the sequence space `ℕ → ℝ` collapse to `𝔠`.

Sorry-free and axiom-free.
-/
import Mathlib

namespace CantorDiagonalizationOQ05

open Cardinal

/-- **`𝔠 ^ ℵ₀ = 𝔠`.** The continuum is fixed by countable exponentiation. This is Mathlib's
`Cardinal.continuum_power_aleph0` (`(2 ^ ℵ₀) ^ ℵ₀ = 2 ^ (ℵ₀ * ℵ₀) = 2 ^ ℵ₀`). It is the
engine behind every statement below, and the countable-power analogue of OQ-07's
`continuum_mul_self : 𝔠 * 𝔠 = 𝔠`. -/
theorem continuum_pow_aleph0 : (𝔠 : Cardinal) ^ (ℵ₀ : Cardinal) = 𝔠 :=
  Cardinal.continuum_power_aleph0

/-- **`#(ℕ → ℝ) = 𝔠`.** The space of real sequences has cardinality the continuum:
`Cardinal.mk_arrow` expands `#(ℕ → ℝ)` to `#ℝ ^ #ℕ`, `mk_real`/`mk_nat` turn the base and
exponent into `𝔠`/`ℵ₀`, and `continuum_pow_aleph0` collapses `𝔠 ^ ℵ₀` to `𝔠`. -/
theorem mk_seq_real_eq_continuum : #(ℕ → ℝ) = 𝔠 := by
  rw [mk_arrow, lift_uzero, lift_uzero, mk_real, mk_nat, continuum_power_aleph0]

/-- **The sequence space and the line are equinumerous: `#(ℕ → ℝ) = #ℝ`.** A countably
infinite power does not raise cardinality — the strong companion to Cantor's diagonal
result that ℝ strictly exceeds ℕ. Both sides equal `𝔠`. -/
theorem mk_seq_real : #(ℕ → ℝ) = #ℝ := by
  rw [mk_seq_real_eq_continuum, mk_real]

/-- **An explicit bijection `(ℕ → ℝ) ≃ ℝ` exists.** The cardinal equality `#(ℕ → ℝ) = #ℝ`
is, by `Cardinal.eq`, exactly the existence of a bijection between real sequences and the
line. (Classical / non-constructive: the witness comes from the cardinal-arithmetic proof,
not an explicit coding formula.) -/
theorem nonempty_equiv_seq_real : Nonempty ((ℕ → ℝ) ≃ ℝ) :=
  Cardinal.eq.mp mk_seq_real

/-- **Baire space `#(ℕ → ℕ) = 𝔠`.** Even with the *smallest* infinite base, countable
sequences already reach the continuum: `mk_arrow` gives `#ℕ ^ #ℕ = ℵ₀ ^ ℵ₀`, collapsed by
`aleph0_power_aleph0`. So `ℕ → ℕ`, `ℕ → ℝ`, and `ℝ` are all equinumerous. -/
theorem mk_seq_nat_eq_continuum : #(ℕ → ℕ) = 𝔠 := by
  rw [mk_arrow, lift_uzero, mk_nat, aleph0_power_aleph0]

/-- **The general principle.** For any type `α` whose cardinality is sandwiched
`2 ≤ #α ≤ 𝔠`, the countable power collapses: `#(ℕ → α) = 𝔠`. Both `ℝ` (base `𝔠`) and `ℕ`
(base `ℵ₀`) are instances. This is `power_aleph0_of_le_continuum` transported across
`mk_arrow`. -/
theorem mk_seq_eq_continuum {α : Type} (h₁ : 2 ≤ #α) (h₂ : #α ≤ 𝔠) :
    #(ℕ → α) = 𝔠 := by
  rw [mk_arrow, lift_uzero, lift_uzero, mk_nat]
  exact power_aleph0_of_le_continuum h₁ h₂

/-- **Subsumes OQ-07: `#(ℕ → ℝ) = #(ℝ × ℝ)`.** A countable power dominates any finite
product, so the space of real sequences and the plane have the same cardinality — both are
`𝔠`. The right side uses `mk_prod` and `continuum_mul_self` exactly as in OQ-07. -/
theorem mk_seq_real_eq_mk_prod_real : #(ℕ → ℝ) = #(ℝ × ℝ) := by
  rw [mk_seq_real_eq_continuum, mk_prod, lift_id, mk_real, continuum_mul_self]

end CantorDiagonalizationOQ05
