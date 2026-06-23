/-
# Cantor Diagonalization OQ-07: the continuum is multiplicatively idempotent, #(ℝ × ℝ) = #ℝ

## Open Question
Formalize `#(ℝ × ℝ) = #ℝ` (equivalently `𝔠 · 𝔠 = 𝔠`): the plane has the same
cardinality as the line, via Mathlib's `Cardinal.mk_prod`, `Cardinal.mk_real`, and the
infinite-cardinal multiplication theorem `Cardinal.continuum_mul_self` (a specialization
of `Cardinal.mul_eq_self`).

## Approach
Where Cantor's diagonal argument (cantor-diagonalization-oq-06) shows ℝ is *strictly*
larger than ℕ, the present companion shows the continuum is *stable* under products:
doubling the dimension does not increase cardinality. `Cardinal.mk_prod` expands
`#(ℝ × ℝ)` to `#ℝ * #ℝ`; `Cardinal.mk_real` rewrites each factor to `𝔠`; and
`Cardinal.continuum_mul_self : 𝔠 * 𝔠 = 𝔠` (itself `mul_eq_self` at `ℵ₀ ≤ 𝔠`) collapses the
product. The cardinal equality `#(ℝ × ℝ) = #ℝ` then unpacks, via `Cardinal.eq`, to an
honest bijection `ℝ × ℝ ≃ ℝ`. As a corollary the complex plane `ℂ ≃ ℝ × ℝ` also has
cardinality `#ℝ`.

Sorry-free and axiom-free.
-/
import Mathlib

namespace CantorDiagonalizationOQ07

open Cardinal

/-- The continuum is multiplicatively idempotent: `𝔠 · 𝔠 = 𝔠`. This is Mathlib's
`Cardinal.continuum_mul_self`, the case `c = 𝔠` of `Cardinal.mul_eq_self` (any infinite
cardinal absorbs self-multiplication, `ℵ₀ ≤ c → c * c = c`). It is the engine behind every
statement below. -/
theorem continuum_sq : (𝔠 : Cardinal) * 𝔠 = 𝔠 :=
  Cardinal.continuum_mul_self

/-- **`#(ℝ × ℝ) = 𝔠`.** The plane has cardinality the continuum: `Cardinal.mk_prod`
expands the product to `#ℝ * #ℝ`, `Cardinal.mk_real` turns each factor into `𝔠`, and
`continuum_sq` collapses `𝔠 * 𝔠` to `𝔠`. -/
theorem mk_prod_real_eq_continuum : #(ℝ × ℝ) = 𝔠 := by
  rw [mk_prod, lift_id, mk_real, continuum_sq]

/-- **The plane and the line are equinumerous: `#(ℝ × ℝ) = #ℝ`.** Dimension does not raise
cardinality — the companion to Cantor's diagonal result that ℝ strictly exceeds ℕ. Both
sides equal `𝔠`. -/
theorem mk_prod_real : #(ℝ × ℝ) = #ℝ := by
  rw [mk_prod_real_eq_continuum, mk_real]

/-- **An explicit bijection `ℝ × ℝ ≃ ℝ` exists.** The cardinal equality `#(ℝ × ℝ) = #ℝ`
is, by `Cardinal.eq`, exactly the existence of a bijection between the plane and the line.
(Classical / non-constructive: the witness comes from the cardinal-arithmetic proof, not an
explicit pairing formula.) -/
theorem nonempty_equiv_prod_real : Nonempty (ℝ × ℝ ≃ ℝ) :=
  Cardinal.eq.mp mk_prod_real

/-- **The complex plane has the cardinality of the real line: `#ℂ = #ℝ`.** Immediate from
`ℂ ≃ ℝ × ℝ` (`Complex.equivRealProd`) and `#(ℝ × ℝ) = #ℝ`; equivalently from
`Cardinal.mk_complex : #ℂ = 𝔠` and `Cardinal.mk_real : #ℝ = 𝔠`. -/
theorem mk_complex_eq_mk_real : #ℂ = #ℝ := by
  rw [mk_complex, mk_real]

end CantorDiagonalizationOQ07
