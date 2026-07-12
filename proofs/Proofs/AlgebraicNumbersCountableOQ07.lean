/-
  Algebraic Numbers Countable — OQ-07: the algebraic reals are *meagre* (Baire
  category), and category ⊥ measure via the Liouville numbers.

  The parent chain establishes that the algebraic reals are small in three senses:
  cardinality (countable), measure (Lebesgue-null), and dimension (Hausdorff
  dimension `0`).  This file records the one remaining classical smallness notion —
  **Baire category** — and then contrasts it with the Liouville numbers to show
  that measure-smallness and category-smallness are genuinely independent.

  Main results (all `0`-sorry / `0`-axiom on top of Mathlib):

  * `liouville_null` / `liouville_comeagre` — the Liouville numbers are
    Lebesgue-null yet comeagre (residual).
  * `comeagre_setOf_transcendental` — the transcendental reals are comeagre.
  * `isMeagre_setOf_isAlgebraic` — **the algebraic reals are meagre.**  Every
    Liouville number is transcendental (`Liouville.transcendental`) and the
    Liouville numbers are comeagre (`eventually_residual_liouville`), so the
    transcendentals are comeagre and the algebraic reals — their complement — are
    meagre.  The Baire-category counterpart of the parent chain's measure-zero /
    Hausdorff-dimension-zero / countability results: the algebraic reals are small
    in *every* classical sense.
  * `exists_null_comeagre` — a Lebesgue-null comeagre set exists (the Liouville
    numbers), so "measure-null" does **not** imply "meagre".  Category and measure
    diverge; the algebraic reals happen to be small in both, but that is not forced
    by either alone.
-/

import Mathlib

open MeasureTheory Filter

namespace AlgebraicNumbersCountableOQ07

/-- The Liouville numbers are Lebesgue-null (`volume`-measure zero).  Wraps
    Mathlib's `volume_setOf_liouville`. -/
theorem liouville_null : volume {x : ℝ | Liouville x} = 0 :=
  volume_setOf_liouville

/-- The Liouville numbers are comeagre: they form a residual set (they contain a
    dense `Gδ`).  Wraps Mathlib's `eventually_residual_liouville`. -/
theorem liouville_comeagre : {x : ℝ | Liouville x} ∈ residual ℝ :=
  eventually_residual_liouville

/-- **The transcendental reals are comeagre.**  The Liouville numbers are comeagre
    and consist entirely of transcendentals, and `residual ℝ` is upward closed. -/
theorem comeagre_setOf_transcendental : {x : ℝ | Transcendental ℤ x} ∈ residual ℝ := by
  refine Filter.mem_of_superset liouville_comeagre ?_
  intro x hx
  have hL : Liouville x := hx
  exact hL.transcendental

/-- **The algebraic reals are meagre.**  Their complement is the transcendental
    reals, which are comeagre (`comeagre_setOf_transcendental`); by definition of
    `IsMeagre` (`sᶜ ∈ residual`) this is exactly meagreness of the algebraic reals.
    This is the Baire-category counterpart to the measure-zero / Hausdorff-
    dimension-zero / countability smallness of the parent chain. -/
theorem isMeagre_setOf_isAlgebraic : IsMeagre {x : ℝ | IsAlgebraic ℤ x} := by
  show {x : ℝ | IsAlgebraic ℤ x}ᶜ ∈ residual ℝ
  refine Filter.mem_of_superset liouville_comeagre ?_
  intro x hx
  have hL : Liouville x := hx
  exact hL.transcendental

/-- **Category and measure are independent.**  The Liouville numbers form a
    Lebesgue-null yet comeagre set, so a `volume`-null set need not be meagre — the
    two classical notions of "smallness" genuinely diverge.  (The algebraic reals
    are small in both senses; the transcendentals are comeagre but of full measure;
    the Liouville numbers realise the remaining corner: null but comeagre.) -/
theorem exists_null_comeagre : ∃ S : Set ℝ, volume S = 0 ∧ S ∈ residual ℝ :=
  ⟨{x : ℝ | Liouville x}, liouville_null, liouville_comeagre⟩

end AlgebraicNumbersCountableOQ07
