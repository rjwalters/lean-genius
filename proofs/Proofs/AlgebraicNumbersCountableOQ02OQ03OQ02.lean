import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Separation.GDelta
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic
import Proofs.AlgebraicNumbersCountable
import Proofs.AlgebraicRealsMeager

/-!
# The Transcendental Reals are a Dense Gδ — and the Algebraic Reals are not Gδ

## Open Question (algebraic-numbers-countable-oq-02-oq-03-oq-02)

The companion entry `algebraic-reals-meager` (`Proofs/AlgebraicRealsMeager.lean`) proves that
the transcendental reals `{x : ℝ | ¬ IsAlgebraic ℚ x}` are **residual** (comeagre), and hence
dense. Residuality is a *covering* statement: by `mem_residual`, a residual set merely
*contains* some dense `Gδ` subset. It does **not**, on its face, say the transcendentals are
themselves a `Gδ` set.

This entry sharpens the topological picture in two ways:

1. **The transcendentals are themselves a dense `Gδ`** (not just a superset of one). The
   algebraic reals are *countable*, hence an `Fσ` set (a countable union of closed singletons),
   so their complement — the transcendentals — is genuinely `Gδ`. Combined with density
   (inherited from residuality in the Baire space `ℝ`) this upgrades the residual witness in
   `mem_residual` to the set itself: the transcendentals *are* a dense `Gδ`.

2. **The algebraic reals are not a `Gδ` set.** This is the classical descriptive-set-theory
   obstruction (the same argument that shows `ℚ` is not `Gδ`): the algebraic reals are *dense*
   (they contain `ℚ`), and the transcendentals are a *dense `Gδ`* disjoint from them. If the
   algebraic reals were also `Gδ`, two **disjoint dense `Gδ` sets** would have a dense — hence
   nonempty — intersection in the Baire space `ℝ` (`Dense.inter_of_Gδ`), a contradiction.

So the three smallness notions for the algebraic reals are *topologically distinguishable* at
the level of the Borel hierarchy: the algebraic reals are `Fσ` but **not** `Gδ`, whereas the
transcendentals are `Gδ` but not `Fσ`. This is strictly finer information than "meagre vs
comeagre": both an `Fσ` meagre set and the bare statement of residuality are compatible with the
complement being `Gδ`; here we pin down exactly which side of the hierarchy each set lies on.

## Main Results

* `compl_countable_isDenseGδ`: in a nonempty perfect `T1` Baire space, the complement of a
  countable set is a **dense `Gδ`** — the abstract form behind result (1).
* `transcendentalReals_isGδ` / `transcendentalReals_isDenseGδ`: the transcendental reals are a
  (dense) `Gδ` set in `ℝ`.
* `algebraicReals_dense`: the algebraic reals are dense (they contain `ℚ`).
* `not_isGδ_of_dense_of_disjoint_denseGδ`: a dense set disjoint from a dense `Gδ` set is not
  itself `Gδ` (in any nonempty Baire space) — the abstract engine behind result (2).
* `algebraicReals_not_isGδ`: the algebraic reals are **not** a `Gδ` subset of `ℝ`.
-/

open Set Topology

namespace AlgebraicNumbersCountableOQ02OQ03OQ02

/-! ### Abstract layer: countable complements and disjoint dense `Gδ` sets -/

/-- **The complement of a countable set is a dense `Gδ` in a perfect `T1` Baire space.**

Two facts combine. *`Gδ`*: in a `T1` space the complement of a countable set is `Gδ`
(`Set.Countable.isGδ_compl`), because a countable set is a countable union of closed singletons
(an `Fσ` set). *Density*: in a perfect `T1` space a countable set is meagre
(`AlgebraicRealsMeager.countable_isMeagre`), so its complement is residual, and residual sets in
a Baire space are dense (`dense_of_mem_residual`). Thus the complement is *itself* a dense `Gδ`,
strengthening the bare residuality statement (which only guarantees a dense `Gδ` *subset*). -/
theorem compl_countable_isDenseGδ {X : Type*} [TopologicalSpace X] [T1Space X] [PerfectSpace X]
    [BaireSpace X] {s : Set X} (hs : s.Countable) : IsGδ sᶜ ∧ Dense sᶜ :=
  ⟨hs.isGδ_compl, dense_of_mem_residual (AlgebraicRealsMeager.countable_isMeagre hs)⟩

/-- **Two disjoint dense `Gδ` sets cannot coexist in a nonempty Baire space.**

If `s` is dense and `Gδ`, and `t` is a dense `Gδ` set disjoint from `s`, we derive a
contradiction: the intersection of two dense `Gδ` sets is dense (`Dense.inter_of_Gδ`), but
`s ∩ t = ∅` is not dense in a nonempty space. This is the abstract engine showing that a dense
set disjoint from a dense `Gδ` cannot itself be `Gδ`. -/
theorem not_isGδ_of_dense_of_disjoint_denseGδ {X : Type*} [TopologicalSpace X] [BaireSpace X]
    [Nonempty X] {s t : Set X} (hsd : Dense s) (hsg : IsGδ s) (htg : IsGδ t) (htd : Dense t)
    (hdisj : Disjoint s t) : False := by
  have hdense : Dense (s ∩ t) := Dense.inter_of_Gδ hsg htg hsd htd
  rw [hdisj.inter_eq] at hdense
  exact Set.not_nonempty_empty hdense.nonempty

/-! ### Concrete layer: the algebraic and transcendental reals -/

/-- **The transcendental reals are a `Gδ` set in `ℝ`.**

The algebraic reals are countable (`AlgebraicNumbersCountable.algebraic_reals_countable`); in the
`T1` space `ℝ` the complement of a countable set is `Gδ` (`Set.Countable.isGδ_compl`). The
complement of the algebraic reals is exactly the transcendental reals. -/
theorem transcendentalReals_isGδ : IsGδ {x : ℝ | ¬ IsAlgebraic ℚ x} := by
  have h : IsGδ ({x : ℝ | IsAlgebraic ℚ x}ᶜ) :=
    AlgebraicNumbersCountable.algebraic_reals_countable.isGδ_compl
  rwa [compl_setOf] at h

/-- **The transcendental reals are a dense `Gδ`.**

Density is inherited from residuality (`AlgebraicRealsMeager.transcendentalReals_dense`); being
`Gδ` is `transcendentalReals_isGδ`. This upgrades the `mem_residual` witness — which only says a
residual set *contains* a dense `Gδ` — to the statement that the transcendentals *are* one. -/
theorem transcendentalReals_isDenseGδ :
    IsGδ {x : ℝ | ¬ IsAlgebraic ℚ x} ∧ Dense {x : ℝ | ¬ IsAlgebraic ℚ x} :=
  ⟨transcendentalReals_isGδ, AlgebraicRealsMeager.transcendentalReals_dense⟩

/-- **The algebraic reals are dense in `ℝ`.**

They contain the rationals — every `q : ℚ`, cast to `ℝ`, is algebraic over `ℚ`
(`isAlgebraic_rat`) — and the rationals are dense (`Rat.denseRange_cast`). -/
theorem algebraicReals_dense : Dense {x : ℝ | IsAlgebraic ℚ x} := by
  refine Dense.mono ?_ (Rat.denseRange_cast (𝕜 := ℝ))
  rintro _ ⟨q, rfl⟩
  exact isAlgebraic_rat ℚ q

/-- **The algebraic reals are NOT a `Gδ` subset of `ℝ`.**

The classical Baire-category obstruction. The algebraic reals are dense (`algebraicReals_dense`)
and the transcendental reals are a dense `Gδ` (`transcendentalReals_isDenseGδ`) disjoint from
them. Were the algebraic reals also `Gδ`, the two disjoint dense `Gδ` sets would have a dense —
hence nonempty — intersection (`not_isGδ_of_dense_of_disjoint_denseGδ`), which is impossible.

Equivalently: the algebraic reals are an `Fσ` set that is not `Gδ`, and dually the transcendental
reals are a `Gδ` set that is not `Fσ`. The countability of the algebraic reals therefore pins
their exact location in the Borel hierarchy, not merely their Baire category. -/
theorem algebraicReals_not_isGδ : ¬ IsGδ {x : ℝ | IsAlgebraic ℚ x} := by
  intro hg
  refine not_isGδ_of_dense_of_disjoint_denseGδ algebraicReals_dense hg
    transcendentalReals_isGδ AlgebraicRealsMeager.transcendentalReals_dense ?_
  rw [Set.disjoint_left]
  intro x hx hx'
  exact hx' hx

end AlgebraicNumbersCountableOQ02OQ03OQ02

#print axioms AlgebraicNumbersCountableOQ02OQ03OQ02.compl_countable_isDenseGδ
#print axioms AlgebraicNumbersCountableOQ02OQ03OQ02.transcendentalReals_isDenseGδ
#print axioms AlgebraicNumbersCountableOQ02OQ03OQ02.algebraicReals_not_isGδ
