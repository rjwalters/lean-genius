import Mathlib

/-
  Measure versus Category: the algebraic reals are null, yet comeagreness
  and conullness disagree
  (algebraic-reals-meager — OQ-02)

  The parent gallery entry ("The Algebraic Reals are Meagre") proves the
  *topological* smallness of the algebraic reals: they are meagre (a
  countable union of nowhere-dense sets), so the transcendentals are
  comeagre (residual) and dense. This file develops the **measure-theoretic**
  counterpart and pins down how the two notions of "size" relate.

  ## The two notions of largeness

  A subset of `ℝ` can be "large" in two independent senses:
  - **topologically large** = *comeagre* (residual): its complement is meagre;
  - **measure-theoretically large** = *conull*: its complement is Lebesgue-null.

  For the algebraic / transcendental dichotomy the two notions agree and
  reinforce each other:

  - `algebraicReals_null`     : the algebraic reals are Lebesgue-null
                                (measure counterpart of the parent's
                                 meagreness);
  - `ae_transcendental`       : almost every real is transcendental
                                (the transcendentals are conull — measure
                                 large — matching the parent's "comeagre").

  But the two notions are *not equivalent*. The Liouville numbers are the
  classical separating example:

  - `liouville_residual`      : the Liouville numbers are comeagre
                                (topologically large);
  - `liouville_null`          : the Liouville numbers are Lebesgue-null
                                (measure-theoretically small);
  - `exists_residual_dense_null` (**headline**): there is a dense, comeagre
                                subset of `ℝ` of measure zero. Hence
                                *comeagre does not imply conull*: topological
                                largeness and measure largeness are genuinely
                                independent.

  The abstract reason behind the separation is the orthogonality of the two
  σ-ideals on `ℝ`:

  - `residual_ae_disjoint`    : `Disjoint (residual ℝ) (ae volume)` — a set
                                cannot be simultaneously "comeagre-large" and
                                "null-large" as filters; the comeagre filter
                                and the a.e. filter share no nontrivial set.

  ## Honesty / novelty

  All ingredients are already in Mathlib (`Algebraic.countable`,
  `Set.Countable.measure_zero`, `eventually_residual_liouville`,
  `volume_setOf_liouville`, `Real.disjoint_residual_ae`). The contribution
  of this entry is the *synthesis*: it assembles the measure side of the
  parent's category result and exhibits the sharp-boundary phenomenon —
  comeagre ⇏ conull, witnessed concretely by the Liouville numbers — which
  the parent (a purely Baire-category entry) does not record. There is no new
  mathematics here; the value is the explicit, machine-checked statement of
  the measure/category contrast.

  No new axioms (standard Mathlib triple inherited).

  References:
  - Oxtoby, J.C. (1980). "Measure and Category", Springer GTM 2 (the
    measure/category duality and the role of Liouville numbers).
  - Mathlib: NumberTheory.Transcendental.Liouville.{Residual,Measure},
             Algebra.AlgebraicCard.

  Tags: measure-theory, baire-category, liouville-numbers, residual,
        transcendental-numbers, lebesgue-measure, sharp-boundary
-/

set_option maxHeartbeats 400000

namespace AlgebraicRealsMeagerOQ02

open MeasureTheory Filter

-- ============================================================================
-- Part I: the measure side of the parent's meagreness result
-- ============================================================================

/-- **The algebraic reals are Lebesgue-null.** Being countable
    (`Algebraic.countable`), the algebraic reals carry no Lebesgue mass, since
    `volume` has no atoms. This is the measure-theoretic counterpart of the
    parent's "the algebraic reals are meagre". -/
theorem algebraicReals_null : volume {x : ℝ | IsAlgebraic ℚ x} = 0 :=
  (Algebraic.countable ℚ ℝ).measure_zero volume

/-- **Almost every real is transcendental.** Equivalently, the transcendentals
    are conull (measure-theoretically large), matching the parent's result
    that they are comeagre. -/
theorem ae_transcendental : ∀ᵐ x : ℝ, ¬ IsAlgebraic ℚ x := by
  filter_upwards [compl_mem_ae_iff.mpr algebraicReals_null] with x hx
  exact hx

-- ============================================================================
-- Part II: Liouville numbers — comeagre yet null
-- ============================================================================

/-- The Liouville numbers are comeagre (residual) in `ℝ`. -/
theorem liouville_residual : {x : ℝ | Liouville x} ∈ residual ℝ :=
  eventually_residual_liouville

/-- The Liouville numbers are dense in `ℝ`. -/
theorem liouville_dense : Dense {x : ℝ | Liouville x} :=
  dense_liouville

/-- The Liouville numbers are Lebesgue-null. -/
theorem liouville_null : volume {x : ℝ | Liouville x} = 0 :=
  volume_setOf_liouville

-- ============================================================================
-- Part III: the sharp boundary — comeagre does not imply conull
-- ============================================================================

/-- **Comeagre ⇏ conull.** There is a dense, comeagre (residual) subset of `ℝ`
    that nevertheless has Lebesgue measure zero. The Liouville numbers witness
    it: topological largeness and measure-theoretic largeness are genuinely
    independent notions of "size". -/
theorem exists_residual_dense_null :
    ∃ S : Set ℝ, S ∈ residual ℝ ∧ Dense S ∧ volume S = 0 :=
  ⟨{x : ℝ | Liouville x}, liouville_residual, liouville_dense, liouville_null⟩

/-- **Orthogonality of the two ideals.** On `ℝ` the comeagre filter
    `residual ℝ` and the almost-everywhere filter `ae volume` are disjoint:
    no nontrivial set is both comeagre and conull-detected by the same filter.
    This is the abstract reason a single set can be comeagre while its
    complement is conull (as for the Liouville numbers and their complement). -/
theorem residual_ae_disjoint : Disjoint (residual ℝ) (ae volume) :=
  Real.disjoint_residual_ae

-- ============================================================================
-- Part IV: OQ-02 resolution
-- ============================================================================

/-- **OQ-02 resolution.** The measure-theoretic counterpart to the parent's
    category result, together with the sharp-boundary phenomenon:

    (1) the algebraic reals are Lebesgue-null (so the transcendentals are
        conull, mirroring "the transcendentals are comeagre"), and
    (2) comeagreness and conullness are nevertheless independent — there is a
        dense comeagre set (the Liouville numbers) of measure zero. -/
theorem oq02_resolution :
    volume {x : ℝ | IsAlgebraic ℚ x} = 0 ∧
    (∃ S : Set ℝ, S ∈ residual ℝ ∧ Dense S ∧ volume S = 0) :=
  ⟨algebraicReals_null, exists_residual_dense_null⟩

#check @algebraicReals_null
#check @ae_transcendental
#check @liouville_residual
#check @liouville_null
#check @exists_residual_dense_null
#check @residual_ae_disjoint
#check @oq02_resolution

/-
  ## Results Summary

  | Theorem | Statement | Status |
  |---------|-----------|--------|
  | `algebraicReals_null` | algebraic reals are Lebesgue-null | Proved |
  | `ae_transcendental` | a.e. real is transcendental | Proved |
  | `liouville_residual` | Liouville numbers comeagre | Proved (Mathlib) |
  | `liouville_dense` | Liouville numbers dense | Proved (Mathlib) |
  | `liouville_null` | Liouville numbers Lebesgue-null | Proved (Mathlib) |
  | `exists_residual_dense_null` | ∃ dense comeagre null set (comeagre ⇏ conull) | Proved |
  | `residual_ae_disjoint` | `Disjoint (residual ℝ) (ae volume)` | Proved (Mathlib) |
  | `oq02_resolution` | measure side + sharp boundary | Proved |

  **Sorries**: 0
  **Axioms**: 0 declared (Mathlib triple inherited)
-/

end AlgebraicRealsMeagerOQ02
