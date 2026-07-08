import Mathlib

/-
  The dual Oxtoby phenomenon: a *meagre* set of *full* Lebesgue measure
  (algebraic-reals-meager — OQ-02 → OQ-01)

  The parent entry OQ-02 ("Measure versus Category") records one half of the
  Oxtoby measure/category contrast: there is a set that is **comeagre**
  (topologically large) yet **null** (measure-theoretically small) — the
  Liouville numbers `L = {x | Liouville x}`. Concretely `L ∈ residual ℝ`
  (`liouville_residual`) while `volume L = 0` (`liouville_null`).

  This file supplies the **dual** direction, completing the symmetric picture:
  there is a set that is **meagre** (topologically small) yet **conull**
  (measure-theoretically large, i.e. of full Lebesgue measure). No new
  construction is needed — the witness is simply the *complement of the
  Liouville numbers*, the **non-Liouville reals** `Lᶜ`:

  - `Lᶜ` is **meagre** because its complement `L` is comeagre
    (`isMeagre_compl_of_mem_residual`);
  - `Lᶜ` is **conull** (`volume (Lᶜ)ᶜ = volume L = 0`) because `L` is null.

  Together with the parent's result this yields the full **symmetric Oxtoby
  decomposition** of the real line:

      ℝ  =  L  ⊔  Lᶜ
            └ comeagre & null      (topologically large, measure-small)
                 └ meagre & conull (topologically small, measure-large)

  i.e. `ℝ` splits into a comeagre null set and a meagre conull set. This is the
  sharp statement that "topological largeness" and "measure largeness" are not
  merely inequivalent (OQ-02) but *complementary*: the very same partition
  witnesses both failures of implication at once.

  ## Honesty / novelty

  Every ingredient is standard Mathlib (`eventually_residual_liouville`,
  `volume_setOf_liouville`, `IsMeagre`, `compl_compl`). The abstract duality
  lemma `isMeagre_compl_of_mem_residual` (complement of a residual set is
  meagre) is a two-line unfolding of the definition `IsMeagre s := sᶜ ∈
  residual`. The mathematical content is the *synthesis*: turning the parent's
  comeagre-null witness into a meagre-conull one by complementation, and
  packaging the resulting symmetric decomposition of `ℝ`. There is no new
  mathematics; the value is the explicit, machine-checked dual statement that
  the parent (which only records the comeagre-null half) leaves implicit.

  No new axioms (standard Mathlib triple inherited).

  References:
  - Oxtoby, J.C. (1980). "Measure and Category", Springer GTM 2.
  - Mathlib: NumberTheory.Transcendental.Liouville.{Residual,Measure},
             Topology.GDelta.Basic (`IsMeagre`).

  Tags: measure-theory, baire-category, liouville-numbers, meagre, residual,
        lebesgue-measure, sharp-boundary, oxtoby-duality
-/

set_option maxHeartbeats 400000

namespace AlgebraicRealsMeagerOQ02OQ01

open MeasureTheory Filter Set

-- ============================================================================
-- Part I: the abstract duality — the complement of a residual set is meagre
-- ============================================================================

/-- **Complement of a comeagre set is meagre.** By definition `IsMeagre s`
    means `sᶜ ∈ residual`; for `s = Aᶜ` this is `Aᶜᶜ = A ∈ residual`. Thus any
    comeagre (residual) set has a meagre complement. This is the structural
    engine that converts the parent's comeagre-null witness into a
    meagre-conull one. -/
theorem isMeagre_compl_of_mem_residual {α : Type*} [TopologicalSpace α]
    {A : Set α} (h : A ∈ residual α) : IsMeagre Aᶜ := by
  rw [IsMeagre, compl_compl]
  exact h

-- ============================================================================
-- Part II: the Liouville numbers (comeagre & null) — recalled from Mathlib
-- ============================================================================

/-- The Liouville numbers are comeagre (residual) in `ℝ`. -/
theorem liouville_residual : {x : ℝ | Liouville x} ∈ residual ℝ :=
  eventually_residual_liouville

/-- The Liouville numbers are Lebesgue-null. -/
theorem liouville_null : volume {x : ℝ | Liouville x} = 0 :=
  volume_setOf_liouville

-- ============================================================================
-- Part III: the dual witness — the non-Liouville reals are meagre yet conull
-- ============================================================================

/-- **The non-Liouville reals are meagre.** Their complement is the comeagre
    set of Liouville numbers, so `isMeagre_compl_of_mem_residual` applies. This
    is the topological "smallness" half of the dual phenomenon. -/
theorem nonLiouville_meagre : IsMeagre {x : ℝ | Liouville x}ᶜ :=
  isMeagre_compl_of_mem_residual liouville_residual

/-- **The non-Liouville reals are conull (of full Lebesgue measure).** Their
    complement is the null set of Liouville numbers, so the complement carries
    no Lebesgue mass. This is the measure-theoretic "largeness" half. -/
theorem nonLiouville_conull : volume ({x : ℝ | Liouville x}ᶜ)ᶜ = 0 := by
  rw [compl_compl]
  exact liouville_null

/-- **Dual Oxtoby (headline).** There exists a *meagre* subset of `ℝ` whose
    complement is Lebesgue-null — a topologically small set of full Lebesgue
    measure. This is the mirror image of the parent's comeagre null set, and
    completes the OQ-02 measure/category contrast in both directions. -/
theorem exists_meagre_conull :
    ∃ S : Set ℝ, IsMeagre S ∧ volume Sᶜ = 0 :=
  ⟨{x : ℝ | Liouville x}ᶜ, nonLiouville_meagre, nonLiouville_conull⟩

-- ============================================================================
-- Part IV: the symmetric Oxtoby decomposition of the real line
-- ============================================================================

/-- **The symmetric Oxtoby decomposition.** The real line partitions into two
    pieces that witness the *complementary* failure of "topological size" and
    "measure size" to coincide:

    * `A = L` — the Liouville numbers: **comeagre** (`A ∈ residual ℝ`) and
      **null** (`volume A = 0`); topologically large, measure-small;
    * `B = Lᶜ` — the non-Liouville reals: **meagre** (`IsMeagre B`) and
      **conull** (`volume Bᶜ = 0`); topologically small, measure-large.

    with `A ∪ B = univ` and `Disjoint A B`. This is the sharp form of OQ-02:
    the two notions of largeness are not merely inequivalent but exactly
    complementary along a single partition of `ℝ`. -/
theorem real_symmetric_oxtoby :
    ∃ A B : Set ℝ,
      A ∪ B = univ ∧ Disjoint A B ∧
      (A ∈ residual ℝ ∧ volume A = 0) ∧
      (IsMeagre B ∧ volume Bᶜ = 0) :=
  ⟨{x : ℝ | Liouville x}, {x : ℝ | Liouville x}ᶜ,
    union_compl_self _, disjoint_compl_right,
    ⟨liouville_residual, liouville_null⟩,
    ⟨nonLiouville_meagre, nonLiouville_conull⟩⟩

/-- **OQ-01 resolution.** Packaging: the dual meagre-conull witness together
    with the full symmetric decomposition of `ℝ`. -/
theorem oq01_resolution :
    (∃ S : Set ℝ, IsMeagre S ∧ volume Sᶜ = 0) ∧
    (∃ A B : Set ℝ,
      A ∪ B = univ ∧ Disjoint A B ∧
      (A ∈ residual ℝ ∧ volume A = 0) ∧
      (IsMeagre B ∧ volume Bᶜ = 0)) :=
  ⟨exists_meagre_conull, real_symmetric_oxtoby⟩

#check @isMeagre_compl_of_mem_residual
#check @nonLiouville_meagre
#check @nonLiouville_conull
#check @exists_meagre_conull
#check @real_symmetric_oxtoby
#check @oq01_resolution

/-
  ## Results Summary

  | Theorem | Statement | Status |
  |---------|-----------|--------|
  | `isMeagre_compl_of_mem_residual` | complement of a residual set is meagre | Proved |
  | `liouville_residual` | Liouville numbers comeagre | Proved (Mathlib) |
  | `liouville_null` | Liouville numbers Lebesgue-null | Proved (Mathlib) |
  | `nonLiouville_meagre` | non-Liouville reals are meagre | Proved |
  | `nonLiouville_conull` | non-Liouville reals are conull (full measure) | Proved |
  | `exists_meagre_conull` | ∃ meagre set of full measure (dual Oxtoby) | Proved |
  | `real_symmetric_oxtoby` | ℝ = comeagre-null ⊔ meagre-conull | Proved |
  | `oq01_resolution` | dual witness + symmetric decomposition | Proved |

  **Sorries**: 0
  **Axioms**: 0 declared (Mathlib triple inherited)
-/

end AlgebraicRealsMeagerOQ02OQ01
