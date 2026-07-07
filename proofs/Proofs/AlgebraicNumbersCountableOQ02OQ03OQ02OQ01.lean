/-
# Dense countable sets are `Fσ` but not `Gδ` in perfect Polish spaces

The parent entry `algebraic-numbers-countable-oq-02-oq-03-oq-02` proves the *concrete*
dichotomy in `ℝ`: the algebraic reals are an `Fσ` set that is not `Gδ`, while the
transcendentals are a dense `Gδ` that is not `Fσ`.  The engine of the "not `Gδ`" half is
pure Baire category and has nothing to do with `ℝ` or algebraicity:

> a dense countable set `D` in a nonempty perfect Polish (indeed any nonempty perfect
> `T1` Baire) space is `Fσ` but **not** `Gδ`,

because `Dᶜ` is then a *dense* `Gδ` (the countable `D` is meagre in a perfect Baire
space, so its complement is comeagre, hence a dense `Gδ`), and two disjoint dense `Gδ`
sets cannot coexist in a nonempty Baire space (their intersection would be dense yet
empty).

This file records that abstraction once and for all, quantified over an arbitrary
topological space carrying the minimal instances that make the argument run
(`T1Space`, `PerfectSpace`, `BaireSpace`, `Nonempty`), and recovers the classical
`ℚ ⊆ ℝ` instance as a one-line corollary.  Every step is a direct assembly of the
already-verified parent lemmas:

* `AlgebraicRealsMeagerDenseGDeltaOQ01.isFσ_of_countable` — a countable set in a `T1`
  space is `Fσ` (the union of its closed singletons);
* `AlgebraicNumbersCountableOQ02OQ03OQ02.compl_countable_isDenseGδ` — the complement of
  a countable set in a perfect `T1` Baire space is a dense `Gδ`;
* `AlgebraicNumbersCountableOQ02OQ03OQ02.not_isGδ_of_dense_of_disjoint_denseGδ` — two
  disjoint dense `Gδ` sets are impossible in a nonempty Baire space.

## Status: verified

Machine-checked with `./proofs/scripts/docker-build.sh
Proofs.AlgebraicNumbersCountableOQ02OQ03OQ02OQ01` (Mathlib 4.26.0): builds cleanly with 0
sorries and no axioms beyond the standard `propext`/`Classical.choice`/`Quot.sound`.  (It
was originally written build-pending during a tool outage; this session build-verifies it
and adds the gallery entry.)

## References
- Kechris, *Classical Descriptive Set Theory*, §8 (Borel hierarchy, Baire category).
- Oxtoby, *Measure and Category*, Ch. 1–2.
-/
import Proofs.AlgebraicNumbersCountableOQ02OQ03OQ02
import Proofs.AlgebraicRealsMeagerDenseGDeltaOQ01
import Mathlib.Topology.Instances.Rat
import Mathlib.Tactic

open Set Topology
open AlgebraicRealsMeagerDenseGDeltaOQ01 AlgebraicNumbersCountableOQ02OQ03OQ02

namespace AlgebraicNumbersCountableOQ02OQ03OQ02OQ01

/-- **Dense countable ⇒ `Fσ` and not `Gδ` (abstract form).**
In any nonempty perfect `T1` Baire space, a countable *dense* set `D` is `Fσ` but not
`Gδ`.  The `Fσ` part is `isFσ_of_countable` (union of closed singletons); the "not `Gδ`"
part is Baire category: if `D` were `Gδ` then `D` and `Dᶜ` would be two *disjoint dense
`Gδ`* sets (`Dᶜ` is a dense `Gδ` by `compl_countable_isDenseGδ`), which
`not_isGδ_of_dense_of_disjoint_denseGδ` rules out. -/
theorem dense_countable_isFσ_and_not_isGδ
    {X : Type*} [TopologicalSpace X] [T1Space X] [PerfectSpace X] [BaireSpace X]
    [Nonempty X] {D : Set X} (hcount : D.Countable) (hdense : Dense D) :
    IsFσ D ∧ ¬ IsGδ D := by
  refine ⟨isFσ_of_countable hcount, ?_⟩
  intro hGδ
  obtain ⟨hgc, hdc⟩ := compl_countable_isDenseGδ hcount
  exact not_isGδ_of_dense_of_disjoint_denseGδ hdense hGδ hgc hdc disjoint_compl_right

/-- A dense countable set in a nonempty perfect `T1` Baire space is `Fσ`. -/
theorem isFσ_of_dense_countable
    {X : Type*} [TopologicalSpace X] [T1Space X] [PerfectSpace X] [BaireSpace X]
    [Nonempty X] {D : Set X} (hcount : D.Countable) (hdense : Dense D) : IsFσ D :=
  (dense_countable_isFσ_and_not_isGδ hcount hdense).1

/-- A dense countable set in a nonempty perfect `T1` Baire space is **not** `Gδ`. -/
theorem not_isGδ_of_dense_countable
    {X : Type*} [TopologicalSpace X] [T1Space X] [PerfectSpace X] [BaireSpace X]
    [Nonempty X] {D : Set X} (hcount : D.Countable) (hdense : Dense D) : ¬ IsGδ D :=
  (dense_countable_isFσ_and_not_isGδ hcount hdense).2

/-! ### The dual (`Gδ`-only) side and the packaged dichotomy -/

/-- **The complement of a dense countable set is `Gδ` but not `Fσ`** — the dual half of the
dichotomy.

*`Gδ`*: immediate from `compl_countable_isDenseGδ`. *Not `Fσ`*: were the complement `Fσ`, its
complement — the original set — would be `Gδ` (`IsFσ.isGδ_compl` together with `compl_compl`),
contradicting `dense_countable_isFσ_and_not_isGδ`. -/
theorem dense_countable_compl_isGδ_not_isFσ
    {X : Type*} [TopologicalSpace X] [T1Space X] [PerfectSpace X] [BaireSpace X]
    [Nonempty X] {D : Set X} (hcount : D.Countable) (hdense : Dense D) :
    IsGδ Dᶜ ∧ ¬ IsFσ Dᶜ := by
  refine ⟨(compl_countable_isDenseGδ hcount).1, fun hf => ?_⟩
  have hs : IsGδ D := by
    have h := hf.isGδ_compl
    rwa [compl_compl] at h
  exact (dense_countable_isFσ_and_not_isGδ hcount hdense).2 hs

/-- **The complete generic dichotomy.** A dense countable set and its complement sit on
opposite, `Fσ`-only and `Gδ`-only, sides of the Borel hierarchy: `D` is `Fσ` but not `Gδ`,
while `Dᶜ` is `Gδ` but not `Fσ`. -/
theorem dense_countable_gδ_fσ_dichotomy
    {X : Type*} [TopologicalSpace X] [T1Space X] [PerfectSpace X] [BaireSpace X]
    [Nonempty X] {D : Set X} (hcount : D.Countable) (hdense : Dense D) :
    (IsFσ D ∧ ¬ IsGδ D) ∧ (IsGδ Dᶜ ∧ ¬ IsFσ Dᶜ) :=
  ⟨dense_countable_isFσ_and_not_isGδ hcount hdense,
    dense_countable_compl_isGδ_not_isFσ hcount hdense⟩

/-! ### The classical `ℚ ⊆ ℝ` instance -/

/-- **`ℚ` is `Fσ` but not `Gδ` in `ℝ`.** The rationals are the range of the (countable,
dense-range) coercion `ℚ → ℝ`, and `ℝ` is a nonempty perfect `T1` Baire space, so the
abstract theorem applies verbatim. This is the classical fact that the rationals sit at
level exactly `Σ⁰₂ ∖ Π⁰₂` of the Borel hierarchy. -/
theorem rationals_isFσ_and_not_isGδ :
    IsFσ (Set.range ((↑) : ℚ → ℝ)) ∧ ¬ IsGδ (Set.range ((↑) : ℚ → ℝ)) :=
  dense_countable_isFσ_and_not_isGδ (Set.countable_range _) Rat.denseRange_cast

end AlgebraicNumbersCountableOQ02OQ03OQ02OQ01

-- Axiom audit (salvaged from PR #34683): expect only propext / Classical.choice / Quot.sound.
#print axioms AlgebraicNumbersCountableOQ02OQ03OQ02OQ01.dense_countable_compl_isGδ_not_isFσ
#print axioms AlgebraicNumbersCountableOQ02OQ03OQ02OQ01.dense_countable_gδ_fσ_dichotomy
