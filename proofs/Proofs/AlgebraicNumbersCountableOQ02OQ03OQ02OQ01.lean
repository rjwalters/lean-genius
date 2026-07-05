import Mathlib.Tactic
import Proofs.AlgebraicNumbersCountableOQ02OQ03OQ02
import Proofs.AlgebraicRealsMeagerDenseGDeltaOQ01
import Proofs.AlgebraicRealsMeager

/-!
# Generic theorem: a dense countable set is `Fσ` but not `Gδ` in a perfect Polish space

## Open Question (algebraic-numbers-countable-oq-02-oq-03-oq-02-oq-01)

The parent entry `algebraic-numbers-countable-oq-02-oq-03-oq-02`
(`Proofs/AlgebraicNumbersCountableOQ02OQ03OQ02.lean`) established, for the *specific* countable
dense set of algebraic reals inside `ℝ`, the two-sided Borel-hierarchy picture: the algebraic
reals are `Fσ` but not `Gδ`, while the transcendentals are `Gδ` but not `Fσ`. Its proof already
isolated the two purely topological engines behind the phenomenon:

* `compl_countable_isDenseGδ` — in a perfect `T1` Baire space the complement of a countable set
  is a *dense* `Gδ`; and
* `not_isGδ_of_dense_of_disjoint_denseGδ` — two disjoint dense `Gδ` sets cannot coexist in a
  nonempty Baire space.

Together with the `Fσ` machinery of the sibling `AlgebraicRealsMeagerDenseGDeltaOQ01`
(`isFσ_of_countable`, `IsFσ.isGδ_compl`), those engines are enough to state and prove the
phenomenon **generically**: the concrete facts about `ℝ` and `IsAlgebraic ℚ` play no role. This
entry records the abstract theorem and specialises it to a *perfect Polish space* — the natural
home of the classical descriptive-set-theory statement — recovering `ℚ ⊆ ℝ` and the
algebraic-reals dichotomy as one-line instances.

It is a *consolidation* result: the mathematical content already lives in the two parents; the
value is a single citable lemma quantified over every perfect Polish space, plus the previously
unstated `ℚ`-is-not-`Gδ` instance and the packaged dual/`Gδ`-side statement.

## Why this is the right level of generality

The phenomenon needs exactly four hypotheses on the ambient space `X`:

* `T1Space X` — singletons are closed, so a countable set is a countable union of *closed*
  singletons (an `Fσ`);
* `PerfectSpace X` — no isolated points, so each singleton is *nowhere dense* and a countable set
  is meagre (its complement is then a dense `Gδ`);
* `BaireSpace X` — the Baire category theorem, so two dense `Gδ` sets meet densely;
* `Nonempty X` — to rule out the vacuous space.

A **nonempty perfect Polish space** supplies all four (`T1` via metrizability, `BaireSpace` via
complete metrizability — see `AlgebraicRealsMeager.t1Space_of_polishSpace` /
`baireSpace_of_polishSpace`), so the Polish statement is a clean corollary of the abstract one.
Displaying the abstract version makes explicit that *completeness and separability are not the
active hypotheses* — perfectness plus the Baire property is the whole story, so the result also
covers `ℝⁿ`, the Cantor space `2^ℕ`, and the Baire space `ℕ^ℕ`.

## Main results

* `dense_countable_isFσ_not_isGδ` — abstract form: in a nonempty perfect `T1` Baire space, a
  dense countable set is `Fσ` but not `Gδ`.
* `dense_countable_compl_isGδ_not_isFσ` — the dual: its complement is `Gδ` but not `Fσ`.
* `dense_countable_gδ_fσ_dichotomy` — the two packaged together (the full four-way split).
* `dense_countable_isFσ_not_isGδ_polish` / `dense_countable_gδ_fσ_dichotomy_polish` — the
  same statements for a nonempty perfect Polish space, with `T1`/`Baire` supplied by instance
  resolution.
* `rat_not_isGδ` — `ℚ` (as `Set.range ((↑) : ℚ → ℝ)`) is not `Gδ` in `ℝ`; a genuinely new
  instance the parents never stated.
* `algebraicReals_isFσ_not_isGδ` — the parent's algebraic-reals result recovered as a one-line
  instance (`ℝ` is a nonempty perfect Polish space).

Consolidates and supersedes the never-committed scratch draft
`research/problems/algebraic-numbers-countable-oq-02-oq-03-oq-02-oq-01/lean/DenseCountableFsigmaNotGdelta.lean`
(researcher-14, 2026-07-04), completing its flagged "move into `proofs/Proofs/`" handoff and
adding the dual / packaged / Polish-specialised statements.
-/

open Set Topology
open AlgebraicRealsMeagerDenseGDeltaOQ01 (IsFσ isFσ_of_countable)
open AlgebraicNumbersCountableOQ02OQ03OQ02
  (compl_countable_isDenseGδ not_isGδ_of_dense_of_disjoint_denseGδ algebraicReals_dense)

namespace AlgebraicNumbersCountableOQ02OQ03OQ02OQ01

/-! ### Abstract layer: dense countable sets in a perfect `T1` Baire space -/

/-- **A dense countable set is `Fσ` but not `Gδ`.**

*`Fσ`*: in a `T1` space a countable set is the countable union of its closed singletons
(`isFσ_of_countable`); density is not needed for this half. *Not `Gδ`*: the complement of the
countable set is a dense `Gδ` (`compl_countable_isDenseGδ`), and it is disjoint from the (dense,
by hypothesis) set itself; if the set were also `Gδ` we would have two disjoint dense `Gδ` sets in
a nonempty Baire space, impossible by `not_isGδ_of_dense_of_disjoint_denseGδ`. -/
theorem dense_countable_isFσ_not_isGδ {X : Type*} [TopologicalSpace X] [T1Space X]
    [PerfectSpace X] [BaireSpace X] [Nonempty X] {s : Set X}
    (hcount : s.Countable) (hdense : Dense s) : IsFσ s ∧ ¬ IsGδ s := by
  refine ⟨isFσ_of_countable hcount, fun hg => ?_⟩
  obtain ⟨hgc, hdc⟩ := compl_countable_isDenseGδ hcount
  exact not_isGδ_of_dense_of_disjoint_denseGδ hdense hg hgc hdc disjoint_compl_right

/-- **The complement of a dense countable set is `Gδ` but not `Fσ`** — the dual half of the
dichotomy.

*`Gδ`*: immediate from `compl_countable_isDenseGδ`. *Not `Fσ`*: were the complement `Fσ`, its
complement — the original set — would be `Gδ` (`IsFσ.isGδ_compl` together with `compl_compl`),
contradicting `dense_countable_isFσ_not_isGδ`. -/
theorem dense_countable_compl_isGδ_not_isFσ {X : Type*} [TopologicalSpace X] [T1Space X]
    [PerfectSpace X] [BaireSpace X] [Nonempty X] {s : Set X}
    (hcount : s.Countable) (hdense : Dense s) : IsGδ sᶜ ∧ ¬ IsFσ sᶜ := by
  refine ⟨(compl_countable_isDenseGδ hcount).1, fun hf => ?_⟩
  have hs : IsGδ s := by
    have h := hf.isGδ_compl
    rwa [compl_compl] at h
  exact (dense_countable_isFσ_not_isGδ hcount hdense).2 hs

/-- **The complete generic dichotomy.** A dense countable set and its complement sit on opposite,
`Fσ`-only and `Gδ`-only, sides of the Borel hierarchy. This is the abstract statement of which the
parent's `algebraic_gδ_fσ_dichotomy` is the `ℝ`/`IsAlgebraic ℚ` instance. -/
theorem dense_countable_gδ_fσ_dichotomy {X : Type*} [TopologicalSpace X] [T1Space X]
    [PerfectSpace X] [BaireSpace X] [Nonempty X] {s : Set X}
    (hcount : s.Countable) (hdense : Dense s) :
    (IsFσ s ∧ ¬ IsGδ s) ∧ (IsGδ sᶜ ∧ ¬ IsFσ sᶜ) :=
  ⟨dense_countable_isFσ_not_isGδ hcount hdense,
    dense_countable_compl_isGδ_not_isFσ hcount hdense⟩

/-! ### Polish specialisation

A nonempty perfect Polish space supplies the `T1` and `BaireSpace` instances automatically, so the
abstract theorems apply verbatim. -/

/-- **A dense countable set in a nonempty perfect Polish space is `Fσ` but not `Gδ`.** The
`T1Space` and `BaireSpace` hypotheses of `dense_countable_isFσ_not_isGδ` are discharged by
instance resolution from `PolishSpace X` (metrizability and complete metrizability). -/
theorem dense_countable_isFσ_not_isGδ_polish {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [PerfectSpace X] [Nonempty X] {s : Set X}
    (hcount : s.Countable) (hdense : Dense s) : IsFσ s ∧ ¬ IsGδ s :=
  dense_countable_isFσ_not_isGδ hcount hdense

/-- **The full dichotomy in a nonempty perfect Polish space.** -/
theorem dense_countable_gδ_fσ_dichotomy_polish {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [PerfectSpace X] [Nonempty X] {s : Set X}
    (hcount : s.Countable) (hdense : Dense s) :
    (IsFσ s ∧ ¬ IsGδ s) ∧ (IsGδ sᶜ ∧ ¬ IsFσ sᶜ) :=
  dense_countable_gδ_fσ_dichotomy hcount hdense

/-! ### Concrete instances in `ℝ` -/

/-- **The rationals are not a `Gδ` subset of `ℝ`.** `ℚ` is countable (`Set.countable_range`) and
dense (`Rat.denseRange_cast`), and `ℝ` is a nonempty perfect `T1` Baire space, so this is the
`X := ℝ`, `s := range ((↑) : ℚ → ℝ)` instance of the abstract theorem. This is the classical fact
that motivates the whole family; the parents proved the algebraic-reals case but never `ℚ`
directly. -/
theorem rat_not_isGδ : ¬ IsGδ (Set.range ((↑) : ℚ → ℝ)) :=
  (dense_countable_isFσ_not_isGδ (s := Set.range ((↑) : ℚ → ℝ))
    (Set.countable_range _) Rat.denseRange_cast).2

/-- **The algebraic reals are `Fσ` but not `Gδ`, as a one-line instance of the generic theorem.**

`ℝ` is a nonempty perfect Polish space; the algebraic reals are countable
(`AlgebraicNumbersCountable.algebraic_reals_countable`) and dense
(`AlgebraicNumbersCountableOQ02OQ03OQ02.algebraicReals_dense`, they contain `ℚ`). So the generic
theorem specialises directly, reproving the parent's
`AlgebraicRealsMeagerDenseGDeltaOQ01.algebraicReals_isFσ` and
`AlgebraicNumbersCountableOQ02OQ03OQ02.algebraicReals_not_isGδ` in one stroke. -/
theorem algebraicReals_isFσ_not_isGδ :
    IsFσ {x : ℝ | IsAlgebraic ℚ x} ∧ ¬ IsGδ {x : ℝ | IsAlgebraic ℚ x} :=
  dense_countable_isFσ_not_isGδ
    AlgebraicNumbersCountable.algebraic_reals_countable algebraicReals_dense

end AlgebraicNumbersCountableOQ02OQ03OQ02OQ01

#print axioms AlgebraicNumbersCountableOQ02OQ03OQ02OQ01.dense_countable_isFσ_not_isGδ
#print axioms AlgebraicNumbersCountableOQ02OQ03OQ02OQ01.dense_countable_compl_isGδ_not_isFσ
#print axioms AlgebraicNumbersCountableOQ02OQ03OQ02OQ01.dense_countable_gδ_fσ_dichotomy_polish
#print axioms AlgebraicNumbersCountableOQ02OQ03OQ02OQ01.rat_not_isGδ
#print axioms AlgebraicNumbersCountableOQ02OQ03OQ02OQ01.algebraicReals_isFσ_not_isGδ
