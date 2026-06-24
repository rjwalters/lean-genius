import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Baire.Lemmas
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic
import Proofs.AlgebraicRealsMeagerDenseGDelta
import Proofs.AlgebraicNumbersCountable

/-!
# A fully constructive transcendental Gδ — explicit decreasing dense-open sequence

## Open Question (algebraic-reals-meager-dense-gdelta-oq-02)

The parent entry `algebraic-reals-meager-dense-gdelta` proves that the **transcendental** reals
form a dense `Gδ` (`transcendentalReals_dense_isGδ`), but only *abstractly*: the witnessing
`IsGδ` is produced by `IsGδ.biInter_of_isOpen` over the *uncountably-indexed-looking* family of
complements `{a}ᶜ` ranging over all algebraic reals `a`. Nothing in that argument hands you an
honest sequence `U : ℕ → Set ℝ` you could enumerate.

This entry answers the second open question:

> "Make the transcendental Gδ fully constructive: an explicit *decreasing* sequence of
>  dense open sets `Uₙ` whose intersection is *exactly* the transcendentals."

Fix any enumeration `algEnum : ℕ → ℝ` of the (countable, nonempty) algebraic reals and set

    U n  :=  (algEnum '' Set.Iic n)ᶜ      -- ℝ minus the first `n+1` enumerated algebraics.

Each `U n` is the complement of a finite set, hence:

* **open** — finite sets are closed in the `T1` space `ℝ`;
* **dense** — `ℝ` is a perfect Baire space, so the complement of any countable (here finite)
  set is dense (parent's `dense_compl_of_countable`);
* **decreasing** — `Set.Iic` is monotone in `n`, so the removed sets grow and the `Uₙ` shrink.

Their intersection strips out *every* enumerated algebraic, leaving exactly the transcendentals:

    ⋂ n, U n  =  {x | ¬ IsAlgebraic ℚ x}.

This upgrades the parent's bare `IsGδ` witness to a concrete antitone basis, and re-derives the
`Gδ` property `transcendentalReals_isGδ` directly from the explicit sequence.

## Main results

* `algEnum`            : an enumeration of the algebraic reals (`range = algebraic reals`).
* `U`                  : the explicit decreasing sequence `(algEnum '' Iic n)ᶜ`.
* `U_isOpen`           : every `U n` is open.
* `U_dense`            : every `U n` is dense.
* `U_antitone`         : the sequence is decreasing.
* `iInter_U`           : **the headline** — `⋂ n, U n` is *exactly* the transcendentals.
* `transcendentalReals_isGδ_of_U` : the transcendentals are `Gδ`, re-derived from `U`.
* `transcendentalReals_constructive_dense_Gδ` : the packaged constructive statement.
-/

open Set Topology

namespace AlgebraicRealsMeagerDenseGDeltaOQ02

/-! ### An enumeration of the algebraic reals -/

/-- **An enumeration of the algebraic reals.** The algebraic reals are countable
(`AlgebraicNumbersCountable.algebraic_reals_countable`) and nonempty (`0` is algebraic), so they
are the range of some sequence `ℕ → ℝ`. -/
noncomputable def algEnum : ℕ → ℝ :=
  (AlgebraicNumbersCountable.algebraic_reals_countable.exists_eq_range
    ⟨0, isAlgebraic_zero⟩).choose

/-- The range of `algEnum` is exactly the set of algebraic reals. -/
theorem algEnum_range : {x : ℝ | IsAlgebraic ℚ x} = Set.range algEnum :=
  (AlgebraicNumbersCountable.algebraic_reals_countable.exists_eq_range
    ⟨0, isAlgebraic_zero⟩).choose_spec

/-! ### The explicit decreasing sequence of dense open sets -/

/-- **The explicit sequence.** `U n` is `ℝ` with the first `n + 1` enumerated algebraic reals
removed. -/
noncomputable def U (n : ℕ) : Set ℝ := (algEnum '' Set.Iic n)ᶜ

/-- The finite set removed at stage `n`. -/
theorem removed_finite (n : ℕ) : (algEnum '' Set.Iic n).Finite :=
  (Set.finite_Iic n).image algEnum

/-- **Each `U n` is open** — it is the complement of a finite (hence closed) set. -/
theorem U_isOpen (n : ℕ) : IsOpen (U n) :=
  isOpen_compl_iff.mpr (removed_finite n).isClosed

/-- **Each `U n` is dense** — the complement of a countable set in the perfect Baire space `ℝ`
is dense (parent `dense_compl_of_countable`). -/
theorem U_dense (n : ℕ) : Dense (U n) :=
  AlgebraicRealsMeagerDenseGDelta.dense_compl_of_countable (removed_finite n).countable

/-- **The sequence is decreasing.** As `n` grows we remove more points, so the `U n` shrink. -/
theorem U_antitone : Antitone U := fun _ _ h =>
  compl_subset_compl.mpr (Set.image_mono (Set.Iic_subset_Iic.mpr h))

/-- **The headline.** The intersection of the explicit sequence is *exactly* the transcendentals:
every algebraic real `algEnum k` is removed at stage `k`, and nothing else is removed. -/
theorem iInter_U : ⋂ n, U n = {x : ℝ | ¬ IsAlgebraic ℚ x} := by
  have hUnion : (⋃ n, algEnum '' Set.Iic n) = {x : ℝ | IsAlgebraic ℚ x} := by
    rw [← Set.image_iUnion]
    have hIic : (⋃ n : ℕ, Set.Iic n) = Set.univ := by
      ext k
      simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_univ, iff_true]
      exact ⟨k, le_refl k⟩
    rw [hIic, Set.image_univ, ← algEnum_range]
  unfold U
  rw [← Set.compl_iUnion, hUnion, Set.compl_setOf]

/-! ### Consequences -/

/-- **The transcendentals are `Gδ`, re-derived constructively** from the explicit open sequence
`U`, rather than from the abstract `biInter` family of the parent. -/
theorem transcendentalReals_isGδ_of_U : IsGδ {x : ℝ | ¬ IsAlgebraic ℚ x} := by
  rw [← iInter_U]
  exact IsGδ.iInter_of_isOpen U_isOpen

/-- **The packaged constructive statement.** There is an explicit decreasing sequence of dense
open subsets of `ℝ` whose intersection is precisely the transcendental reals — the fully
constructive form of the parent's dense-`Gδ` theorem. -/
theorem transcendentalReals_constructive_dense_Gδ :
    (∀ n, IsOpen (U n)) ∧ (∀ n, Dense (U n)) ∧ Antitone U ∧
      ⋂ n, U n = {x : ℝ | ¬ IsAlgebraic ℚ x} :=
  ⟨U_isOpen, U_dense, U_antitone, iInter_U⟩

#print axioms transcendentalReals_constructive_dense_Gδ
#print axioms transcendentalReals_isGδ_of_U

end AlgebraicRealsMeagerDenseGDeltaOQ02
