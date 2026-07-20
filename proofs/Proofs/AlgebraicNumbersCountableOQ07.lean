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

/-! ### The measure–category duality on `ℝ` (the four corners)

`exists_null_comeagre` records one corner of the classical measure/category
square: a set that is Lebesgue-null yet comeagre (the Liouville numbers).  The
**dual corner** — a set that is *meagre* yet of *full measure* — is realised by
the complement, the non-Liouville numbers: it is meagre (complement of the
comeagre Liouville set) and co-null (complement of the null Liouville set).

Splitting `ℝ` along `Liouville`/`¬Liouville` then gives a completely explicit,
choice-and-`CH`-free instance of the **Sierpiński–Erdős measure–category
duality**: the real line is the disjoint union of a meagre set and a null set.
No single notion of "smallness" (measure vs. category) refines the other — a fact
the parent chain's *algebraic* reals (small in *both* senses) cannot witness, but
this Liouville splitting does. -/

/-- **The non-Liouville reals are meagre.**  Their complement is the Liouville
    set, which is comeagre (`liouville_comeagre`); by the definition of `IsMeagre`
    (`sᶜ ∈ residual`) this is exactly meagreness.  The category counterpart of
    `not_liouville_conull` and the dual of `liouville_comeagre`. -/
theorem not_liouville_meagre : IsMeagre {x : ℝ | ¬ Liouville x} := by
  show {x : ℝ | ¬ Liouville x}ᶜ ∈ residual ℝ
  have hcompl : {x : ℝ | ¬ Liouville x}ᶜ = {x : ℝ | Liouville x} := by
    simp [Set.compl_setOf]
  rw [hcompl]
  exact liouville_comeagre

/-- **The non-Liouville reals have full measure** (their complement is null).  The
    complement is the Liouville set, which is Lebesgue-null (`liouville_null`); so
    the non-Liouville reals are co-null.  The measure counterpart of
    `not_liouville_meagre`. -/
theorem not_liouville_conull : volume {x : ℝ | ¬ Liouville x}ᶜ = 0 := by
  have hcompl : {x : ℝ | ¬ Liouville x}ᶜ = {x : ℝ | Liouville x} := by
    simp [Set.compl_setOf]
  rw [hcompl]
  exact liouville_null

/-- **The dual corner: a meagre set of full measure exists.**  The non-Liouville
    reals are meagre (`not_liouville_meagre`) yet co-null (`not_liouville_conull`),
    so "meagre" does **not** imply "null".  Together with `exists_null_comeagre`
    (null but comeagre) this fills the two off-diagonal corners of the
    measure/category square: neither notion of smallness implies the other. -/
theorem exists_meagre_conull : ∃ S : Set ℝ, IsMeagre S ∧ volume Sᶜ = 0 :=
  ⟨{x : ℝ | ¬ Liouville x}, not_liouville_meagre, not_liouville_conull⟩

/-- **The Sierpiński–Erdős decomposition of `ℝ`.**  The real line is the disjoint
    union of a meagre set `A` (the non-Liouville reals) and a Lebesgue-null set `B`
    (the Liouville reals).  An entirely explicit, `CH`-free witness that measure
    and category are independent notions of largeness: `ℝ` itself is "small" in
    each of the two senses on complementary pieces, so no set can be simultaneously
    "large" in both on all of `ℝ`. -/
theorem exists_meagre_null_decomposition :
    ∃ A B : Set ℝ, IsMeagre A ∧ volume B = 0 ∧ A ∪ B = Set.univ ∧ Disjoint A B := by
  refine ⟨{x : ℝ | ¬ Liouville x}, {x : ℝ | Liouville x}, not_liouville_meagre,
    liouville_null, ?_, ?_⟩
  · ext x
    by_cases h : Liouville x <;> simp [h]
  · rw [Set.disjoint_left]
    intro x hx hx'
    exact hx hx'

/-! ### Descriptive-set structure: `Gδ` vs. not-`Gδ` (the `ℚ`/irrationals pattern)

Everything above is a *category* statement (meagre / comeagre / residual).  The
finer **Borel-hierarchy** structure is that the algebraic reals sit inside `ℝ`
exactly as `ℚ` does: being countable they are an `Fσ` set, so the transcendentals
— their complement — form a *dense `Gδ`* (strengthening the mere comeagreness of
`comeagre_setOf_transcendental` to the transcendentals actually *being* a dense
`Gδ`).  Dually, the algebraic reals are **not** a `Gδ` set — the exact analogue of
the classical "`ℚ` is `Fσ` but not `Gδ`".  If they were `Gδ`, then being dense
they would be residual (`residual_of_dense_Gδ`); but they are meagre
(`isMeagre_setOf_isAlgebraic`), and in the nonempty Baire space `ℝ` no set is
simultaneously residual and meagre (`not_isMeagre_of_mem_residual`). -/

/-- **Every rational real is algebraic over `ℤ`.**  `q = q.num / q.den` is a root
    of the nonzero integer polynomial `C q.den · X − C q.num` (nonzero because its
    degree-`1` coefficient is `q.den ≠ 0`).  Supplies a dense set of algebraic
    reals for `dense_setOf_isAlgebraic`. -/
theorem isAlgebraic_ratCast (q : ℚ) : IsAlgebraic ℤ ((q : ℝ)) := by
  refine ⟨Polynomial.C (q.den : ℤ) * Polynomial.X - Polynomial.C q.num, ?_, ?_⟩
  · intro hp
    have h1 : (Polynomial.C (q.den : ℤ) * Polynomial.X - Polynomial.C q.num).coeff 1
        = (q.den : ℤ) := by
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_one,
        mul_one, Polynomial.coeff_C, if_neg (one_ne_zero), sub_zero]
    rw [hp, Polynomial.coeff_zero] at h1
    exact q.den_nz (by exact_mod_cast h1.symm)
  · have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
    have he : (Polynomial.aeval (q : ℝ))
        (Polynomial.C (q.den : ℤ) * Polynomial.X - Polynomial.C q.num)
        = (q.den : ℝ) * (q : ℝ) - (q.num : ℝ) := by
      simp
    rw [he, Rat.cast_def]
    field_simp
    ring

/-- **The algebraic reals are dense.**  They contain every rational cast
    (`isAlgebraic_ratCast`) and the rationals are dense in `ℝ`
    (`Rat.denseRange_cast`). -/
theorem dense_setOf_isAlgebraic : Dense {x : ℝ | IsAlgebraic ℤ x} :=
  Dense.mono (Set.range_subset_iff.mpr fun q => isAlgebraic_ratCast q) Rat.denseRange_cast

/-- **The algebraic reals are not a `Gδ` set** — the descriptive-set analogue of
    "`ℚ` is not `Gδ`".  A dense `Gδ` set is residual (`residual_of_dense_Gδ`), but
    the algebraic reals are meagre (`isMeagre_setOf_isAlgebraic`), and a nonempty
    Baire space has no set that is both residual and meagre
    (`not_isMeagre_of_mem_residual`).  So no matter how the algebraic reals are
    presented, they cannot be a countable intersection of open sets. -/
theorem not_isGδ_setOf_isAlgebraic : ¬ IsGδ {x : ℝ | IsAlgebraic ℤ x} := by
  intro hGδ
  have hres : {x : ℝ | IsAlgebraic ℤ x} ∈ residual ℝ :=
    residual_of_dense_Gδ hGδ dense_setOf_isAlgebraic
  exact not_isMeagre_of_mem_residual hres isMeagre_setOf_isAlgebraic

/-- **The transcendental reals are a dense `Gδ`.**  The algebraic reals are
    countable (`Algebraic.countable ℤ ℝ`), hence `Fσ`, so their complement — the
    transcendentals — is `Gδ` (`Set.Countable.isGδ_compl`); density is
    `dense_setOf_transcendental`.  This upgrades `comeagre_setOf_transcendental`
    (comeagre means *containing* a dense `Gδ`) to the transcendentals themselves
    *being* a dense `Gδ`. -/
theorem isGδ_setOf_transcendental : IsGδ {x : ℝ | Transcendental ℤ x} := by
  have hcompl : {x : ℝ | Transcendental ℤ x} = {x : ℝ | IsAlgebraic ℤ x}ᶜ := by
    ext x; simp [Transcendental, Set.mem_compl_iff, Set.mem_setOf_eq]
  rw [hcompl]
  exact (Algebraic.countable ℤ ℝ).isGδ_compl

/-- **Capstone.**  The algebraic/transcendental split of `ℝ` reproduces the Borel
    structure of the `ℚ`/irrationals split: the transcendentals are a dense `Gδ`
    while the algebraic reals, though `Fσ`, are not `Gδ`.  This is a strictly
    sharper separation than the measure/category corners above — it distinguishes
    the two sets at the level of the Borel hierarchy, not just Baire category. -/
theorem transcendental_isGδ_and_algebraic_not_isGδ :
    IsGδ {x : ℝ | Transcendental ℤ x} ∧ ¬ IsGδ {x : ℝ | IsAlgebraic ℤ x} :=
  ⟨isGδ_setOf_transcendental, not_isGδ_setOf_isAlgebraic⟩

/-! ### Complex analogue: the `Gδ` / not-`Gδ` dichotomy in `ℂ`

The category results already crossed to `ℂ` (`isMeagre_setOf_isAlgebraic_complex`,
`dense_setOf_transcendental_complex`).  The finer **Borel-hierarchy** dichotomy transfers too:
the transcendental complex numbers are a `Gδ` set, while the algebraic ones — though `Fσ`
(countable) — are **not** `Gδ`, exactly as in `ℝ`.  The `Gδ` half is identical bookkeeping
(`Algebraic.countable ℤ ℂ` ⟹ `Fσ` ⟹ complement `Gδ`).  The not-`Gδ` half needs *density of the
algebraic numbers in `ℂ`*, which — unlike `ℝ`, where `ℚ` alone suffices — has no analogue in the
parent chain and is not in Mathlib.  We supply it via the **Gaussian rationals** `ℚ + ℚ·i`: each
`a + b·i` with `a, b ∈ ℚ` is algebraic over `ℤ` (`IsAlgebraic.add`/`.mul` applied to
`isAlgebraic_ratCast_complex` and `isAlgebraic_I`), and they are dense because `ℚ` is dense along
both the real and imaginary axes.  All axiom-free. -/

/-- **`i` is algebraic over `ℤ`.**  It is a root of `X² + 1` (`Complex.I_sq : I² = -1`); the
    polynomial is nonzero since its degree-`2` coefficient is `1`. -/
theorem isAlgebraic_I : IsAlgebraic ℤ Complex.I := by
  refine ⟨Polynomial.X ^ 2 + 1, ?_, ?_⟩
  · intro h
    have hc := congrArg (fun p => Polynomial.coeff p 2) h
    simp [Polynomial.coeff_one] at hc
  · simp [Complex.I_sq]

/-- **Every rational, cast into `ℂ`, is algebraic over `ℤ`.**  `q = q.num / q.den` is a root of
    the nonzero integer polynomial `C q.den · X − C q.num`.  The `ℂ`-valued companion of
    `isAlgebraic_ratCast`, supplying the real parts of the Gaussian rationals. -/
theorem isAlgebraic_ratCast_complex (q : ℚ) : IsAlgebraic ℤ ((q : ℂ)) := by
  refine ⟨Polynomial.C (q.den : ℤ) * Polynomial.X - Polynomial.C q.num, ?_, ?_⟩
  · intro hp
    have h1 : (Polynomial.C (q.den : ℤ) * Polynomial.X - Polynomial.C q.num).coeff 1
        = (q.den : ℤ) := by
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_one,
        mul_one, Polynomial.coeff_C, if_neg (one_ne_zero), sub_zero]
    rw [hp, Polynomial.coeff_zero] at h1
    exact q.den_nz (by exact_mod_cast h1.symm)
  · have hden : (q.den : ℂ) ≠ 0 := by exact_mod_cast q.den_nz
    have he : (Polynomial.aeval (q : ℂ))
        (Polynomial.C (q.den : ℤ) * Polynomial.X - Polynomial.C q.num)
        = (q.den : ℂ) * (q : ℂ) - (q.num : ℂ) := by simp
    rw [he, Rat.cast_def]
    field_simp
    ring

/-- **The complex algebraic numbers are dense.**  The Gaussian rationals `a + b·i`
    (`a, b ∈ ℚ`) are algebraic over `ℤ` (`isAlgebraic_ratCast_complex`, `isAlgebraic_I`,
    `IsAlgebraic.add`/`.mul`) and dense in `ℂ`: given `z` and `r > 0`, pick `a, b ∈ ℚ` with
    `|z.re − a|, |z.im − b| < r/2` (`Rat.denseRange_cast`), so
    `‖z − (a + b·i)‖ ≤ |z.re − a| + |z.im − b| < r` (`Complex.norm_le_abs_re_add_abs_im`). -/
theorem dense_setOf_isAlgebraic_complex : Dense {z : ℂ | IsAlgebraic ℤ z} := by
  rw [Metric.dense_iff]
  intro z r hr
  have hr2 : (0 : ℝ) < r / 2 := by positivity
  obtain ⟨a, ha⟩ := Metric.denseRange_iff.mp Rat.denseRange_cast z.re (r / 2) hr2
  obtain ⟨b, hb⟩ := Metric.denseRange_iff.mp Rat.denseRange_cast z.im (r / 2) hr2
  rw [Real.dist_eq] at ha hb
  refine ⟨(a : ℂ) + (b : ℂ) * Complex.I, ?_, ?_⟩
  · rw [Metric.mem_ball, Complex.dist_eq]
    have hre : ((a : ℂ) + (b : ℂ) * Complex.I - z).re = (a : ℝ) - z.re := by simp
    have him : ((a : ℂ) + (b : ℂ) * Complex.I - z).im = (b : ℝ) - z.im := by simp
    calc ‖(a : ℂ) + (b : ℂ) * Complex.I - z‖
        ≤ |((a : ℂ) + (b : ℂ) * Complex.I - z).re|
            + |((a : ℂ) + (b : ℂ) * Complex.I - z).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = |(a : ℝ) - z.re| + |(b : ℝ) - z.im| := by rw [hre, him]
      _ = |z.re - (a : ℝ)| + |z.im - (b : ℝ)| := by rw [abs_sub_comm (a : ℝ), abs_sub_comm (b : ℝ)]
      _ < r / 2 + r / 2 := by gcongr
      _ = r := by ring
  · exact (isAlgebraic_ratCast_complex a).add ((isAlgebraic_ratCast_complex b).mul isAlgebraic_I)

/-- **The complex algebraic numbers are not `Gδ`.**  A dense `Gδ` set is residual
    (`residual_of_dense_Gδ`, with `dense_setOf_isAlgebraic_complex`), but the algebraic complex
    numbers are meagre (`isMeagre_setOf_isAlgebraic_complex`), and a nonempty Baire space has no
    set that is both residual and meagre (`not_isMeagre_of_mem_residual`).  The `ℂ`-analogue of
    `not_isGδ_setOf_isAlgebraic`. -/
theorem not_isGδ_setOf_isAlgebraic_complex : ¬ IsGδ {z : ℂ | IsAlgebraic ℤ z} := by
  intro hGδ
  have hres : {z : ℂ | IsAlgebraic ℤ z} ∈ residual ℂ :=
    residual_of_dense_Gδ hGδ dense_setOf_isAlgebraic_complex
  exact not_isMeagre_of_mem_residual hres isMeagre_setOf_isAlgebraic_complex

/-- **The complex transcendentals are a dense `Gδ`.**  The algebraic complex numbers are
    countable (`Algebraic.countable ℤ ℂ`), hence `Fσ`, so their complement — the
    transcendentals — is `Gδ` (`Set.Countable.isGδ_compl`).  Upgrades the mere comeagreness
    behind `dense_setOf_transcendental_complex` to the transcendentals *being* a dense `Gδ`. -/
theorem isGδ_setOf_transcendental_complex : IsGδ {z : ℂ | Transcendental ℤ z} := by
  have hcompl : {z : ℂ | Transcendental ℤ z} = {z : ℂ | IsAlgebraic ℤ z}ᶜ := by
    ext z; simp [Transcendental, Set.mem_compl_iff, Set.mem_setOf_eq]
  rw [hcompl]
  exact (Algebraic.countable ℤ ℂ).isGδ_compl

/-- **Complex capstone.**  The algebraic/transcendental split of `ℂ` reproduces the same
    Borel-hierarchy separation as `ℝ` (`transcendental_isGδ_and_algebraic_not_isGδ`): the
    transcendentals are a dense `Gδ` while the algebraic numbers, though `Fσ`, are not `Gδ`.
    Completes the `ℂ`-transfer of the entry's descriptive-set dichotomy, resting on the new
    density of the algebraic numbers in `ℂ` via the Gaussian rationals. -/
theorem transcendental_isGδ_and_algebraic_not_isGδ_complex :
    IsGδ {z : ℂ | Transcendental ℤ z} ∧ ¬ IsGδ {z : ℂ | IsAlgebraic ℤ z} :=
  ⟨isGδ_setOf_transcendental_complex, not_isGδ_setOf_isAlgebraic_complex⟩

end AlgebraicNumbersCountableOQ07
