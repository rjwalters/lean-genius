/-
  SCRATCH / BUILD-UNVERIFIED (2026-07-04, researcher-14)

  Docker build + Aristotle are both down (containerd blob I/O error; Aristotle 404),
  so this file has NOT been compiled. It is a mechanical assembly of lemmas whose
  exact signatures were read from the following COMPILING corpus files:

    * proofs/Proofs/AlgebraicRealsMeagerDenseGDeltaOQ01.lean
        - def IsFσ, theorem isFσ_of_countable  (T1 space, countable ⇒ Fσ)
    * proofs/Proofs/AlgebraicNumbersCountableOQ02OQ03OQ02.lean
        - compl_countable_isDenseGδ            (T1 + Perfect + Baire: sᶜ dense Gδ)
        - not_isGδ_of_dense_of_disjoint_denseGδ (Baire + Nonempty engine)
        - algebraicReals_dense
    * proofs/Proofs/AlgebraicNumbersCountable.lean
        - algebraic_reals_countable

  HANDOFF: once Docker recovers, move this file to proofs/Proofs/, add an
  `import Proofs.DenseCountableFsigmaNotGdelta` line to proofs/Proofs.lean, and run
    ./proofs/scripts/docker-build.sh Proofs.DenseCountableFsigmaNotGdelta
  Expected: 0 sorries, 0 axioms (foundational only). Then create gallery data under
  src/data/proofs/dense-countable-fsigma-not-gdelta/ (meta.json, annotations.json, index.ts).
-/
import Mathlib.Tactic
import Proofs.AlgebraicRealsMeagerDenseGDeltaOQ01
import Proofs.AlgebraicNumbersCountableOQ02OQ03OQ02

/-!
# Dense countable sets are Fσ but not Gδ in perfect Polish spaces

The parent entry (`algebraic-numbers-countable-oq-02-oq-03-oq-02`) proved, for the concrete
algebraic reals in `ℝ`, that a dense countable set is `Fσ` but not `Gδ`. Crucially, it stated the
two engines abstractly (for an arbitrary `X`):

* `compl_countable_isDenseGδ` — in a perfect `T1` Baire space the complement of a countable set
  is a dense `Gδ`;
* `not_isGδ_of_dense_of_disjoint_denseGδ` — in a nonempty Baire space a dense set disjoint from a
  dense `Gδ` cannot itself be `Gδ`.

The sibling `algebraic-reals-meager-dense-gdelta-oq-01` supplied the missing `Fσ` half:

* `IsFσ` (a local dual of Mathlib's `IsGδ` — Mathlib v4.26.0 has no `IsFσ` predicate) and
* `isFσ_of_countable` — in a `T1` space every countable set is `Fσ`.

This entry does the **abstraction the open question asks for**: it packages both halves into one
theorem quantified over *every* perfect Polish space and *every* dense countable subset, then
recovers `ℚ ⊆ ℝ` and the algebraic reals as one-line instances. It is a consolidation result, not
a new idea — the mathematical content already lives in the two parents; the value is removing
duplication and giving the gallery a single citable lemma.

## Main results

* `denseCountable_isFσ_not_isGδ` — the headline: in a nonempty perfect `T1` Baire space, a
  countable dense set is `Fσ` and not `Gδ`.
* `rat_not_isGδ` — `ℚ` (as `Set.range ((↑) : ℚ → ℝ)`) is not `Gδ` in `ℝ` — a genuinely new
  instance the parents did not state.
* `algebraicReals_not_isGδ` — the parent's headline re-derived as a corollary.
-/

open Set Topology
open AlgebraicRealsMeagerDenseGDeltaOQ01 (IsFσ isFσ_of_countable)
open AlgebraicNumbersCountableOQ02OQ03OQ02
  (compl_countable_isDenseGδ not_isGδ_of_dense_of_disjoint_denseGδ)

namespace DenseCountableFsigmaNotGdelta

/-- **Dense countable ⇒ `Fσ` but not `Gδ`, in any nonempty perfect `T1` Baire space.**

`Fσ`: countability alone (with `T1`) gives `Fσ` via `isFσ_of_countable` — the set is the
countable union of its closed singletons.

Not `Gδ`: the complement `Dᶜ` is a *dense* `Gδ` (`compl_countable_isDenseGδ`, using perfectness
so singletons are nowhere dense, hence `D` is meagre and `Dᶜ` residual = dense). If `D` were also
`Gδ`, then `D` (dense) and `Dᶜ` (dense `Gδ`) would be two disjoint dense `Gδ` sets, whose
intersection is dense — impossible in a nonempty space (`not_isGδ_of_dense_of_disjoint_denseGδ`,
with `disjoint_compl_right : Disjoint D Dᶜ`). -/
theorem denseCountable_isFσ_not_isGδ {X : Type*} [TopologicalSpace X] [T1Space X]
    [PerfectSpace X] [BaireSpace X] [Nonempty X] {D : Set X}
    (hcount : D.Countable) (hdense : Dense D) : IsFσ D ∧ ¬ IsGδ D := by
  refine ⟨isFσ_of_countable hcount, fun hGδ => ?_⟩
  obtain ⟨hgδc, hdc⟩ := compl_countable_isDenseGδ hcount
  exact not_isGδ_of_dense_of_disjoint_denseGδ hdense hGδ hgδc hdc disjoint_compl_right

/-- **The rationals are not a `Gδ` subset of `ℝ`.** `ℚ` is countable (`Set.countable_range`) and
dense (`Rat.denseRange_cast`), and `ℝ` is a nonempty perfect `T1` Baire space, so this is the
`X := ℝ`, `D := range ((↑) : ℚ → ℝ)` instance of the headline. This is the classical fact that
motivates the whole family; the parents proved the algebraic-reals case but never `ℚ` directly. -/
theorem rat_not_isGδ : ¬ IsGδ (Set.range ((↑) : ℚ → ℝ)) :=
  (denseCountable_isFσ_not_isGδ (Set.countable_range _) Rat.denseRange_cast).2

/-- **The algebraic reals are not a `Gδ` subset of `ℝ`** — the parent's headline recovered as a
corollary of the abstract theorem, via countability (`algebraic_reals_countable`) and density
(`algebraicReals_dense`). -/
theorem algebraicReals_not_isGδ : ¬ IsGδ {x : ℝ | IsAlgebraic ℚ x} :=
  (denseCountable_isFσ_not_isGδ
      AlgebraicNumbersCountable.algebraic_reals_countable
      AlgebraicNumbersCountableOQ02OQ03OQ02.algebraicReals_dense).2

end DenseCountableFsigmaNotGdelta

#print axioms DenseCountableFsigmaNotGdelta.denseCountable_isFσ_not_isGδ
#print axioms DenseCountableFsigmaNotGdelta.rat_not_isGδ
