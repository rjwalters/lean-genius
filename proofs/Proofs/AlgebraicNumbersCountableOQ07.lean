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

/-- **The transcendental reals are dense.**  A comeagre subset of the Baire space `ℝ` is
    dense (`dense_of_mem_residual`), so `comeagre_setOf_transcendental` immediately gives that
    the transcendentals are dense in `ℝ`: between any two reals lies a transcendental.  The
    topological ubiquity counterpart to the meagreness of the algebraics
    (`isMeagre_setOf_isAlgebraic`). -/
theorem dense_setOf_transcendental : Dense {x : ℝ | Transcendental ℤ x} :=
  dense_of_mem_residual comeagre_setOf_transcendental

/-- **The Liouville numbers are dense.**  Likewise the comeagre Liouville set is dense in
    `ℝ` — every open interval contains a Liouville number — so Baire-smallness of the
    algebraics coexists with a topologically ubiquitous (and Lebesgue-null, by
    `liouville_null`) set of transcendentals. -/
theorem dense_setOf_liouville : Dense {x : ℝ | Liouville x} :=
  dense_of_mem_residual liouville_comeagre

/-! ### The complex algebraic numbers are meagre (Baire category in `ℂ`)

The results above live in `ℝ`, where the Liouville numbers supply an explicit
comeagre set of transcendentals.  The parent chain shows the *complex* algebraic
numbers are small in measure (`algebraic_complex_hausdorffMeasure_zero`) and
dimension (`algebraic_complex_dimH_zero`), but the Baire-category corner in `ℂ`
was missing — there is no complex analogue of the Liouville construction.  It
follows instead from pure **countability**: in a perfect `T₁` space every
singleton is nowhere dense (`interior_singleton`), so any countable set is a
countable union of nowhere-dense singletons, hence meagre.  Both `ℝ` and `ℂ`
are perfect (`T₁ + connected + nontrivial`), and the algebraic numbers over the
countable ring `ℤ` are countable (`Algebraic.countable`). -/

/-- **Every countable set in a perfect `T₁` space is meagre.**  A singleton `{x}`
    is closed (`T₁`) with empty interior (`interior_singleton`, valid because a
    perfect space has no isolated points), hence nowhere dense; a countable set is
    the countable union of its singletons, so it is meagre by `isMeagre_iUnion`. -/
theorem isMeagre_of_countable {X : Type*} [TopologicalSpace X] [T1Space X]
    [PerfectSpace X] {s : Set X} (hs : s.Countable) : IsMeagre s := by
  have hsub : Countable ↥s := hs.to_subtype
  have hcov : s = ⋃ x : s, {(x : X)} := by ext y; simp
  rw [hcov]
  refine isMeagre_iUnion (fun x => ?_)
  rw [isMeagre_iff_countable_union_isNowhereDense]
  refine ⟨{{(x : X)}}, ?_, Set.countable_singleton _, by simp⟩
  intro t ht
  rw [Set.mem_singleton_iff] at ht
  subst ht
  exact isClosed_singleton.isNowhereDense_iff.mpr (interior_singleton (x : X))

/-- **The complex algebraic numbers are meagre.**  The Baire-category counterpart,
    in `ℂ`, of `isMeagre_setOf_isAlgebraic` (which lived only in `ℝ` via Liouville).
    Since `ℂ` is a perfect `T₁` space and the algebraic numbers over the countable
    ring `ℤ` are countable (`Algebraic.countable ℤ ℂ`), meagreness follows from
    `isMeagre_of_countable`.  Together with the parent's complex measure-zero and
    Hausdorff-dimension-zero results, the algebraic complex numbers are small in
    every classical sense. -/
theorem isMeagre_setOf_isAlgebraic_complex : IsMeagre {z : ℂ | IsAlgebraic ℤ z} :=
  isMeagre_of_countable (Algebraic.countable ℤ ℂ)

/-- **The complex transcendentals are dense.**  The complement of the meagre
    complex algebraic numbers is comeagre (residual), and `ℂ` is a Baire space, so
    `dense_of_mem_residual` gives density: every nonempty open subset of `ℂ`
    contains a transcendental.  The complex counterpart of
    `dense_setOf_transcendental`. -/
theorem dense_setOf_transcendental_complex : Dense {z : ℂ | Transcendental ℤ z} := by
  apply dense_of_mem_residual
  show {z : ℂ | IsAlgebraic ℤ z}ᶜ ∈ residual ℂ
  exact isMeagre_setOf_isAlgebraic_complex

end AlgebraicNumbersCountableOQ07
