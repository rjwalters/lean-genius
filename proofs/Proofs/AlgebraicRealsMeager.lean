import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Perfect
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Tactic
import Proofs.AlgebraicNumbersCountable

/-!
# The Algebraic Reals are Meagre (Baire Category)

## Open Question (algebraic-reals-meager)

The companion entry `algebraic-numbers-countable` proves that the algebraic reals
`{x : ℝ | IsAlgebraic ℚ x}` are *countable*, and `algebraic-numbers-countable-oq-02-oq-02`
re-derives the uncountability of `ℝ` by a concrete nested-interval (Baire-category style)
construction, explicitly flagging the *abstract* Baire Category Theorem generalization as
an unformalized follow-up:

> "the abstract Baire Category Theorem (every nonempty complete metric space without
>  isolated points is uncountable) replaces nested intervals with nested open balls
>  avoiding each f(n) … Formalizing this Baire-category generalization in Lean would
>  subsume both this entry and the more general statement."

This entry closes that gap *topologically*: it strengthens "countable" to the strictly
stronger Baire-category statement that the algebraic reals are **meagre** (a set of the
first category) in `ℝ`, and dually that the **transcendental** reals are *comeagre*
(residual) — hence dense. Topological smallness sits alongside the measure-theoretic
smallness (the algebraic reals are Lebesgue-null) and the cardinality smallness
(they are countable):

    algebraic reals  ⊆  ℝ        is simultaneously
      • countable          (cardinality:  ℵ₀ < 𝔠)
      • Lebesgue-null      (measure:      μ = 0)
      • meagre             (Baire category: first category)

while the transcendentals are co-small in all three senses. "Almost every real is
transcendental" therefore holds in the category sense as well, not merely the cardinality
sense.

## Main Results

* `countable_isMeagre`: in any `T1` perfect topological space, every countable set is
  meagre. (The abstract Baire-category lemma requested by the companion entry.)
* `algebraicReals_isMeagre`: `{x : ℝ | IsAlgebraic ℚ x}` is meagre in `ℝ`.
* `transcendentalReals_residual`: `{x : ℝ | ¬ IsAlgebraic ℚ x}` is residual (comeagre).
* `transcendentalReals_dense`: the transcendental reals are dense in `ℝ`.
* `algebraicReals_ne_univ`: the algebraic reals are not all of `ℝ` — transcendentals exist —
  recovered purely from meagreness (a nonempty Baire space is not meagre in itself).

## Proof Strategy

A single point `{x}` is **nowhere dense** in any `T1` perfect space: it is closed, and its
interior is empty because `x` is not isolated (`interior_singleton`, available since `ℝ` is
a `PerfectSpace`). A countable set is a countable union of its singletons, so it is a
countable union of nowhere-dense sets, hence meagre (`isMeagre_iUnion`). Instantiating at
the countable set `{x : ℝ | IsAlgebraic ℚ x}` (Mathlib's `Algebraic.countable`, reused via
`AlgebraicNumbersCountable.algebraic_reals_countable`) gives meagreness; the complement is
then residual, and residual sets in a Baire space (`ℝ` is one) are dense.
-/

open Set Topology

namespace AlgebraicRealsMeager

/-- A nowhere dense set is meagre: it is covered by the singleton family `{t}`,
a one-element (hence countable) family of nowhere-dense sets. -/
theorem isMeagre_of_isNowhereDense {X : Type*} [TopologicalSpace X] {t : Set X}
    (ht : IsNowhereDense t) : IsMeagre t := by
  rw [isMeagre_iff_countable_union_isNowhereDense]
  refine ⟨{t}, ?_, Set.countable_singleton t, ?_⟩
  · intro u hu
    rwa [Set.mem_singleton_iff.mp hu]
  · simpa using (Set.sUnion_singleton t).ge

/-- In a `T1` perfect space a singleton is nowhere dense: it is closed, and its interior is
empty because the point is not isolated (`interior_singleton`). -/
theorem isNowhereDense_singleton {X : Type*} [TopologicalSpace X] [T1Space X]
    [PerfectSpace X] (x : X) : IsNowhereDense ({x} : Set X) :=
  (isClosed_singleton.isNowhereDense_iff).mpr (interior_singleton x)

/-- **Countable sets are meagre in a perfect `T1` space.**

This is the abstract Baire-category lemma underlying the nested-interval construction in the
companion entry `algebraic-numbers-countable-oq-02-oq-02`: a countable set is a countable
union of (nowhere-dense) singletons, hence of the first category. In particular, in any
nonempty `BaireSpace` that is `T1` and perfect (e.g. `ℝ`), a countable set has dense
complement and cannot be the whole space. -/
theorem countable_isMeagre {X : Type*} [TopologicalSpace X] [T1Space X] [PerfectSpace X]
    {s : Set X} (hs : s.Countable) : IsMeagre s := by
  rw [← Set.biUnion_of_singleton s, Set.biUnion_eq_iUnion]
  haveI : Countable s := hs.to_subtype
  exact isMeagre_iUnion fun i => isMeagre_of_isNowhereDense (isNowhereDense_singleton (i : X))

/-- **The algebraic reals are meagre in `ℝ`.**

A strict strengthening of countability: beyond having cardinality `ℵ₀`, the set
`{x : ℝ | IsAlgebraic ℚ x}` is topologically small (of the first Baire category). The
countability input is Mathlib's `Algebraic.countable`, packaged as
`AlgebraicNumbersCountable.algebraic_reals_countable`; `ℝ` is `T1` and a `PerfectSpace`
(connected, `T1`, nontrivial). -/
theorem algebraicReals_isMeagre : IsMeagre {x : ℝ | IsAlgebraic ℚ x} :=
  countable_isMeagre AlgebraicNumbersCountable.algebraic_reals_countable

/-- **The transcendental reals are residual (comeagre).**

The complement of a meagre set is residual, and the complement of the algebraic reals is
exactly the transcendental reals. -/
theorem transcendentalReals_residual : {x : ℝ | ¬ IsAlgebraic ℚ x} ∈ residual ℝ := by
  have h : IsMeagre {x : ℝ | IsAlgebraic ℚ x} := algebraicReals_isMeagre
  rw [IsMeagre, compl_setOf] at h
  exact h

/-- **The transcendental reals are dense in `ℝ`.**

Residual sets in a Baire space are dense; `ℝ` is a Baire space. -/
theorem transcendentalReals_dense : Dense {x : ℝ | ¬ IsAlgebraic ℚ x} :=
  dense_of_mem_residual transcendentalReals_residual

/-- **The algebraic reals are a proper subset of `ℝ`: transcendentals exist.**

Recovered purely from meagreness, with no explicit transcendental construction: a nonempty
Baire space is not meagre in itself, so a meagre set cannot be all of `ℝ`. -/
theorem algebraicReals_ne_univ : {x : ℝ | IsAlgebraic ℚ x} ≠ Set.univ := by
  intro h
  have hmeagre : IsMeagre (Set.univ : Set ℝ) := h ▸ algebraicReals_isMeagre
  have : ¬ IsMeagre (Set.univ : Set ℝ) :=
    not_isMeagre_of_isOpen isOpen_univ Set.univ_nonempty
  exact this hmeagre

/-- There exists a transcendental real number — extracted from `algebraicReals_ne_univ`. -/
theorem exists_transcendental_real : ∃ x : ℝ, ¬ IsAlgebraic ℚ x := by
  by_contra h
  push_neg at h
  exact algebraicReals_ne_univ (Set.eq_univ_of_forall h)

/-- **Abstract Baire-category uncountability.**

A nonempty `T1` perfect Baire space is uncountable: were the whole space countable it would
be meagre in itself (`countable_isMeagre`), contradicting that a nonempty Baire space is not
meagre (`not_isMeagre_of_isOpen` applied to the open set `univ`). This is exactly the abstract
Baire Category Theorem flagged as an unformalized follow-up by the companion nested-interval
entry — "every nonempty complete metric space without isolated points is uncountable" — here
isolated to the genuinely topological hypotheses (`T1` + `PerfectSpace` + `BaireSpace`), with
no metric or completeness assumption beyond what `BaireSpace` packages. -/
theorem not_countable_of_perfect_t1_baire {X : Type*} [TopologicalSpace X] [T1Space X]
    [PerfectSpace X] [BaireSpace X] [Nonempty X] : ¬ (Set.univ : Set X).Countable := by
  intro hcount
  have hmeagre : IsMeagre (Set.univ : Set X) := countable_isMeagre hcount
  exact (not_isMeagre_of_isOpen isOpen_univ Set.univ_nonempty) hmeagre

/-- **`ℝ` is uncountable, recovered abstractly from the Baire-category lemma.**

A non-constructive, category-theoretic proof of Cantor's theorem that the reals are
uncountable: it uses only that `ℝ` is `T1`, perfect (no isolated points), a Baire space, and
nonempty, with no diagonal argument or nested-interval construction. This subsumes the
companion nested-interval entry, whose conclusion is this very statement. -/
theorem not_countable_real : ¬ (Set.univ : Set ℝ).Countable :=
  not_countable_of_perfect_t1_baire

end AlgebraicRealsMeager

#print axioms AlgebraicRealsMeager.algebraicReals_isMeagre
#print axioms AlgebraicRealsMeager.exists_transcendental_real
#print axioms AlgebraicRealsMeager.not_countable_of_perfect_t1_baire
#print axioms AlgebraicRealsMeager.not_countable_real
