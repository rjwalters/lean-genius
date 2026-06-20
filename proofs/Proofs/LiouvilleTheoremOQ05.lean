/-
Liouville's Theorem OQ-05: The Measure–Category Duality of Liouville Numbers

The parent Liouville family establishes that Liouville numbers are transcendental,
form an *uncountable*, indeed *residual* (comeagre, topologically "large") subset
of ℝ, and is closed under translation/scaling by rationals. What it states only as
prose (PART VI, "Borel, 1909") is the measure-theoretic counterpoint:

  • Borel's theorem.   The set of Liouville numbers has **Lebesgue measure zero**.
  • Typicality.        **Almost every** real number fails to be Liouville.

Putting these alongside the topological facts produces one of the cleanest
instances of the **measure–category duality**: the real line splits into two
complementary pieces, each "large" in one sense and "small" in the other.

  • The Liouville numbers are residual (comeagre) yet Lebesgue-null.
  • Dually, the non-Liouville numbers are meagre yet of full measure.

So "topologically generic" (residual) and "measure-typical" (almost-everywhere)
are genuinely different notions of largeness: the two filters `residual ℝ` and
`ae volume` are **disjoint**. The same dichotomy underlies the Erdős–Sierpiński
duality; the Liouville set is the textbook witness.

Main results:
  • `volume_liouville_eq_zero`   — Borel: `volume {x | Liouville x} = 0`.
  • `ae_not_liouville'`          — almost every real number is not Liouville.
  • `exists_residual_null`       — a residual set of measure zero exists (Liouville).
  • `exists_meagre_conull`       — dually, a meagre set whose complement is null.
  • `residual_ae_disjoint`       — `Disjoint (residual ℝ) (ae volume)` (the duality).
  Plus the explicit "large yet null" packaging `liouville_residual_and_null`.

All results are `sorry`-free and axiom-free (no `native_decide`); they assemble
Mathlib's `volume_setOf_liouville`, `ae_not_liouville`, `eventually_residual_liouville`,
and `Real.disjoint_residual_ae` into the duality statement, formalizing the
measure-zero claim the gallery previously carried only as a comment.

References:
- Mathlib `Mathlib/NumberTheory/Transcendental/Liouville/Measure.lean` and `Residual.lean`.
- É. Borel, *Les probabilités dénombrables et leurs applications arithmétiques* (1909).
- Oxtoby, *Measure and Category* (measure–category duality).
-/

import Mathlib.NumberTheory.Transcendental.Liouville.Measure
import Mathlib.NumberTheory.Transcendental.Liouville.Residual
import Mathlib.Tactic

open MeasureTheory Filter Set

namespace LiouvilleTheoremOQ05

/-! ### Borel's theorem: the Liouville set is Lebesgue-null -/

/-- **Borel (1909).** The set of Liouville numbers has Lebesgue measure zero. This
is the measure-theoretic counterpart to the parent entry's topological results, and
formalizes the claim previously stated only as prose. -/
theorem volume_liouville_eq_zero : volume {x : ℝ | Liouville x} = 0 :=
  volume_setOf_liouville

/-- **Almost every real number is not a Liouville number.** Equivalently, the
non-Liouville reals are co-null (form a set of full measure). -/
theorem ae_not_liouville' : ∀ᵐ x : ℝ, ¬ Liouville x :=
  ae_not_liouville

/-! ### The Liouville set: residual yet null -/

/-- The Liouville numbers are *both* residual (comeagre — topologically generic)
*and* Lebesgue-null. This is the key tension exploited below. -/
theorem liouville_residual_and_null :
    {x : ℝ | Liouville x} ∈ residual ℝ ∧ volume {x : ℝ | Liouville x} = 0 :=
  ⟨eventually_residual_liouville, volume_setOf_liouville⟩

/-- **A residual set of measure zero exists.** Topological genericity does not
imply measure-typicality: the Liouville numbers are comeagre yet null. -/
theorem exists_residual_null : ∃ S : Set ℝ, S ∈ residual ℝ ∧ volume S = 0 :=
  ⟨{x : ℝ | Liouville x}, eventually_residual_liouville, volume_setOf_liouville⟩

/-! ### The dual: a meagre set of full measure -/

/-- **A meagre set whose complement is null exists** (equivalently, a meagre set of
full measure). Dually to `exists_residual_null`, measure-typicality does not imply
topological genericity: the non-Liouville reals are meagre yet co-null. The witness
is the complement of the Liouville set. -/
theorem exists_meagre_conull : ∃ S : Set ℝ, IsMeagre S ∧ volume Sᶜ = 0 := by
  refine ⟨{x : ℝ | Liouville x}ᶜ, ?_, ?_⟩
  · -- `IsMeagre Sᶜ` unfolds to `Sᶜᶜ ∈ residual ℝ`, i.e. `{Liouville} ∈ residual ℝ`.
    rw [IsMeagre, compl_compl]
    exact eventually_residual_liouville
  · rw [compl_compl]
    exact volume_setOf_liouville

/-! ### Measure–category duality -/

/-- **Measure–category duality.** The filters `residual ℝ` (topological genericity)
and `ae volume` (measure-typicality) are *disjoint*: no nonempty property can be both
comeagre and almost-everywhere. The disjointness is witnessed concretely by the
Liouville set, which is residual while its complement is co-null. -/
theorem residual_ae_disjoint : Disjoint (residual ℝ) (ae volume) :=
  Real.disjoint_residual_ae

end LiouvilleTheoremOQ05
