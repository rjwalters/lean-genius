/-
# Measure versus Category: the two independent notions of "smallness" on ℝ

The parent entry `algebraic-reals-meager` shows that the algebraic reals
`{x : ℝ | IsAlgebraic ℚ x}` are **meagre** (topologically small, of the first
Baire category), and its measure-theoretic companion shows they are **null**
(Lebesgue measure zero). The algebraic reals are thus small in *both* senses at
once.

This is, however, exceptional rather than typical. The two notions of smallness
— meagre (category) and null (measure) — are genuinely *independent*: a set can
be topologically large yet have measure zero, and topologically small yet have
full measure. The canonical witness is the set of **Liouville numbers**, which
is simultaneously

* **comeagre** (residual): its complement is meagre — Mathlib's
  `eventually_residual_liouville`; and
* **null**: it has Lebesgue measure zero — Mathlib's `volume_setOf_liouville`.

From this single witness we extract:

1. The measure–category independence in both directions (a comeagre null set and
   a meagre conull set), and the abstract statement that the two genericity
   filters `residual ℝ` and `ae volume` are disjoint (`Real.disjoint_residual_ae`).
2. An **Erdős–Sierpiński-style decomposition** `ℝ = A ∪ B` with `A` meagre and
   `B` null — a partition of the line into a topologically negligible piece and a
   measure-negligible piece.
3. A refinement of the parent: since every Liouville number is transcendental,
   the comeagre-yet-null Liouville set sits *inside* the transcendental reals, so
   the transcendentals — already known to be comeagre — contain a comeagre subset
   of measure zero.
4. The capstone contrast: the algebraic reals are small in both senses (meagre
   AND null), while the transcendentals are large in both senses (comeagre AND
   conull) — the special "aligned" case that the Liouville phenomenon shows is
   not forced.

Everything is derived from Mathlib's Liouville machinery and `Algebraic.countable`;
the file is self-contained over Mathlib (no project imports) and uses no axioms
beyond Mathlib's foundational `propext` / `Classical.choice` / `Quot.sound`.

Child of `algebraic-reals-meager-oq-01` (#26822), which packaged the abstract
Baire Category Theorem; this entry instead exploits the *failure* of the two
smallness notions to coincide.
-/
import Mathlib.NumberTheory.Transcendental.Liouville.Residual
import Mathlib.NumberTheory.Transcendental.Liouville.Measure
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Perfect
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

open Set Topology MeasureTheory Filter

namespace AlgebraicRealsMeagerOQ02

-- ============================================================================
-- § 0. Supporting lemmas: countable ⟹ meagre on ℝ
--
-- These mirror the parent entry's helpers but are restated here so the file is
-- self-contained over Mathlib. `ℝ` is `T1` and a `PerfectSpace` (it is `T1`,
-- connected and nontrivial), so singletons are nowhere dense and any countable
-- set is a countable union of them, hence meagre.
-- ============================================================================

/-- A nowhere-dense set is meagre: it is the union of the one-element (hence
countable) family `{t}` of nowhere-dense sets. -/
theorem isMeagre_of_isNowhereDense {t : Set ℝ} (ht : IsNowhereDense t) :
    IsMeagre t := by
  rw [isMeagre_iff_countable_union_isNowhereDense]
  refine ⟨{t}, ?_, Set.countable_singleton t, ?_⟩
  · intro u hu
    rwa [Set.mem_singleton_iff.mp hu]
  · exact (Set.sUnion_singleton t).ge

/-- A singleton in `ℝ` is nowhere dense: it is closed and has empty interior
because `ℝ` has no isolated points (`PerfectSpace`). -/
theorem isNowhereDense_singleton (x : ℝ) : IsNowhereDense ({x} : Set ℝ) :=
  (isClosed_singleton.isNowhereDense_iff).mpr (interior_singleton x)

/-- **Countable subsets of `ℝ` are meagre.** A countable set is a countable union
of nowhere-dense singletons. -/
theorem countable_isMeagre {s : Set ℝ} (hs : s.Countable) : IsMeagre s := by
  rw [← Set.biUnion_of_singleton s, Set.biUnion_eq_iUnion]
  haveI : Countable s := hs.to_subtype
  exact isMeagre_iUnion fun i => isMeagre_of_isNowhereDense (isNowhereDense_singleton (i : ℝ))

-- ============================================================================
-- § 1. The Liouville witness: comeagre yet null
-- ============================================================================

/-- **The Liouville numbers are residual (comeagre).** A residual property holds
on a dense `Gδ`; here it is exactly Mathlib's `eventually_residual_liouville`,
recast as set membership. -/
theorem liouville_residual : {x : ℝ | Liouville x} ∈ residual ℝ :=
  eventually_residual_liouville

/-- **The non-Liouville reals are meagre.** `IsMeagre s` means `sᶜ ∈ residual`,
and the complement of the non-Liouville reals is the (residual) Liouville set. -/
theorem nonLiouville_isMeagre : IsMeagre {x : ℝ | ¬ Liouville x} := by
  rw [IsMeagre, compl_setOf]
  simp only [not_not]
  exact liouville_residual

/-- **The Liouville numbers are null** (Lebesgue measure zero): Mathlib's
`volume_setOf_liouville`. -/
theorem liouville_volume_zero : volume {x : ℝ | Liouville x} = 0 :=
  volume_setOf_liouville

/-- **The Liouville set is comeagre *and* null simultaneously.** This is the core
witness that topological largeness and measure largeness can diverge: a single
set that is residual (topologically "almost all" of `ℝ`) yet has Lebesgue
measure zero (measure-theoretically negligible). -/
theorem liouville_comeagre_and_null :
    {x : ℝ | Liouville x} ∈ residual ℝ ∧ volume {x : ℝ | Liouville x} = 0 :=
  ⟨liouville_residual, liouville_volume_zero⟩

-- ============================================================================
-- § 2. Measure–category independence
-- ============================================================================

/-- **The two genericity filters are disjoint.** `residual ℝ` (topological
genericity) and `ae volume` (measure-theoretic genericity) have trivial
intersection: no nonempty filter refines both, so a single set cannot be
"generic" in both senses with a "generic" complement. This is Mathlib's
`Real.disjoint_residual_ae`; we surface it as the abstract statement underlying
the concrete witnesses below. -/
theorem residual_ae_disjoint : Disjoint (residual ℝ) (ae (volume : Measure ℝ)) :=
  Real.disjoint_residual_ae

/-- **A comeagre set can have measure zero.** Topological genericity does not
imply full measure: the Liouville set is residual yet null. -/
theorem exists_residual_volume_zero :
    ∃ s : Set ℝ, s ∈ residual ℝ ∧ volume s = 0 :=
  ⟨{x : ℝ | Liouville x}, liouville_residual, liouville_volume_zero⟩

/-- **A meagre set can have full measure.** Measure genericity does not imply
topological genericity: the non-Liouville reals are meagre, yet their complement
(the Liouville set) is null, so they have full measure. -/
theorem exists_isMeagre_compl_volume_zero :
    ∃ s : Set ℝ, IsMeagre s ∧ volume sᶜ = 0 := by
  refine ⟨{x : ℝ | ¬ Liouville x}, nonLiouville_isMeagre, ?_⟩
  rw [compl_setOf]
  simp only [not_not]
  exact liouville_volume_zero

/-- **Erdős–Sierpiński-style decomposition.** The real line splits as a disjoint
union `ℝ = A ∪ B` where `A` is meagre (topologically negligible) and `B` is null
(measure-theoretically negligible). One cannot do this with a single notion of
smallness — a Baire space is not meagre in itself, and `ℝ` does not have measure
zero — so the decomposition is precisely a manifestation of measure–category
independence. Here `A` = non-Liouville reals, `B` = Liouville reals. -/
theorem exists_meagre_null_decomposition :
    ∃ A B : Set ℝ, A ∪ B = Set.univ ∧ Disjoint A B ∧ IsMeagre A ∧ volume B = 0 := by
  refine ⟨{x : ℝ | Liouville x}ᶜ, {x : ℝ | Liouville x},
    compl_union_self _, disjoint_compl_left, ?_, liouville_volume_zero⟩
  rw [IsMeagre, compl_compl]
  exact liouville_residual

-- ============================================================================
-- § 3. Tie to the algebraic / transcendental dichotomy
-- ============================================================================

/-- **Every Liouville number is transcendental.** Liouville's theorem gives
transcendence over `ℤ` (`Liouville.transcendental`); transcendence over `ℤ` and
over `ℚ` coincide for real numbers because `ℚ` is the field of fractions of `ℤ`
(`IsFractionRing.isAlgebraic_iff`). Hence the Liouville set is contained in the
transcendental reals. -/
theorem liouville_subset_transcendental :
    {x : ℝ | Liouville x} ⊆ {x : ℝ | ¬ IsAlgebraic ℚ x} := by
  intro x hx
  rw [Set.mem_setOf_eq, ← IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ]
  exact hx.transcendental

/-- **Refinement of the parent.** The parent shows the transcendental reals are
residual. This sharpens that: the transcendentals *contain* a comeagre set that
is also null (the Liouville numbers). So even within the topologically generic
transcendentals there is a residual subset of Lebesgue measure zero. -/
theorem transcendental_contains_comeagre_null :
    ∃ s : Set ℝ, s ⊆ {x : ℝ | ¬ IsAlgebraic ℚ x} ∧
      s ∈ residual ℝ ∧ volume s = 0 :=
  ⟨{x : ℝ | Liouville x}, liouville_subset_transcendental,
    liouville_residual, liouville_volume_zero⟩

-- ============================================================================
-- § 4. Capstone: the algebraic reals are the "aligned" exceptional case
-- ============================================================================

/-- The algebraic reals are meagre (re-derived self-containedly from
`Algebraic.countable` and `countable_isMeagre`). -/
theorem algebraicReals_isMeagre : IsMeagre {x : ℝ | IsAlgebraic ℚ x} :=
  countable_isMeagre (Algebraic.countable ℚ ℝ)

/-- The algebraic reals are null (a countable set has Lebesgue measure zero). -/
theorem algebraicReals_volume_zero : volume {x : ℝ | IsAlgebraic ℚ x} = 0 :=
  (Algebraic.countable ℚ ℝ).measure_zero volume

/-- **The algebraic reals are small in *both* senses.** Unlike the generic
situation exhibited by the Liouville set, the algebraic reals are simultaneously
meagre (category) and null (measure). They are the exceptional "aligned" set
where the two smallness notions agree — a coincidence forced here by mere
countability, not by either notion alone. -/
theorem algebraicReals_meagre_and_null :
    IsMeagre {x : ℝ | IsAlgebraic ℚ x} ∧ volume {x : ℝ | IsAlgebraic ℚ x} = 0 :=
  ⟨algebraicReals_isMeagre, algebraicReals_volume_zero⟩

/-- The transcendental reals are residual (comeagre): the complement of the
meagre algebraic reals. -/
theorem transcendentalReals_residual : {x : ℝ | ¬ IsAlgebraic ℚ x} ∈ residual ℝ := by
  have h := algebraicReals_isMeagre
  rwa [IsMeagre, compl_setOf] at h

/-- **The transcendental reals are large in both senses**, dually to the
algebraic reals being small in both: they are comeagre (category) and conull
(full measure — their complement, the algebraic reals, is null). -/
theorem transcendentalReals_comeagre_and_conull :
    {x : ℝ | ¬ IsAlgebraic ℚ x} ∈ residual ℝ ∧
      volume {x : ℝ | IsAlgebraic ℚ x} = 0 :=
  ⟨transcendentalReals_residual, algebraicReals_volume_zero⟩

end AlgebraicRealsMeagerOQ02
