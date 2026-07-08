import Mathlib

/-
  Both halves of the symmetric Oxtoby decomposition are *dense*
  (algebraic-reals-meager — OQ-02 → OQ-01, structural follow-up)

  The sibling file `AlgebraicRealsMeagerOQ02OQ01` records the **symmetric
  Oxtoby decomposition** of the real line

      ℝ  =  L  ⊔  Lᶜ
            └ comeagre & null      (topologically large, measure-small)
                 └ meagre & conull (topologically small, measure-large)

  where `L = {x | Liouville x}`. That statement contrasts the two notions of
  largeness but says nothing about how the two pieces sit *topologically*
  inside `ℝ`. This file supplies the sharpening: **both** pieces are **dense**.

  * `L` is dense because it is comeagre and `ℝ` is a Baire space
    (`dense_of_mem_residual`). This half is routine.
  * `Lᶜ` is dense — the genuinely informative half — *despite being meagre*.
    A meagre set is topologically "small", yet here it meets every nonempty
    open interval, because it is **conull**: any nonempty open set carries
    positive Lebesgue measure (`volume` is an open-positive measure), so a set
    whose complement is null can have no interior and is therefore dense.

  Consequently `ℝ` is partitioned into **two disjoint dense sets**, one
  comeagre-and-null and one meagre-and-conull. The measure/category pathology
  is not confined to a nowhere-dense corner: both anomalous classes are
  topologically ubiquitous.

  The reusable engine is the abstract lemma `dense_of_conull`: in any space
  whose measure gives nonempty opens positive mass (`IsOpenPosMeasure`), a
  conull set is dense. It is proved from Mathlib's
  `interior_eq_empty_of_null` (a null set has empty interior) via the standard
  `closure = (interior ·ᶜ)ᶜ` identity.

  ## Honesty / novelty

  No new mathematics: `dense_of_conull` is a three-line rearrangement of
  `interior_eq_empty_of_null`, mirroring Mathlib's own `dense_of_ae`, and
  `dense_liouville` is a one-line appeal to `dense_of_mem_residual`. The value
  is the explicit, machine-checked observation that the Oxtoby decomposition is
  a partition of `ℝ` into two dense sets, which the sibling file leaves
  unstated. Presented as a modest structural sharpening, not a new result.

  No new axioms (standard Mathlib triple inherited).

  References:
  - Oxtoby, J.C. (1980). "Measure and Category", Springer GTM 2.
  - Mathlib: MeasureTheory.Measure.OpenPos (`interior_eq_empty_of_null`,
             `IsOpenPosMeasure`), Topology.Baire.Lemmas
             (`dense_of_mem_residual`),
             NumberTheory.Transcendental.Liouville.{Residual,Measure}.

  Tags: measure-theory, baire-category, liouville-numbers, dense, meagre,
        residual, lebesgue-measure, sharp-boundary, oxtoby-duality
-/

set_option maxHeartbeats 400000

namespace AlgebraicRealsMeagerOQ02OQ01Dense

open MeasureTheory Filter Set

-- ============================================================================
-- Part I: the abstract engine — a conull set is dense
-- ============================================================================

/-- **A conull set is dense** (in a space whose measure gives every nonempty
    open set positive mass). If `μ sᶜ = 0` then `s` has dense complement of its
    complement: `interior sᶜ = ∅` (a null set has empty interior), so
    `closure s = (interior sᶜ)ᶜ = univ`. This is the measure-theoretic mirror
    of `dense_of_mem_residual` and the engine that makes the *meagre* half of
    the Oxtoby decomposition dense. -/
theorem dense_of_conull {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} [μ.IsOpenPosMeasure] {s : Set X} (hs : μ sᶜ = 0) :
    Dense s := by
  rw [dense_iff_closure_eq, closure_eq_compl_interior_compl, compl_univ_iff]
  exact μ.interior_eq_empty_of_null hs

-- ============================================================================
-- Part II: the Liouville numbers — comeagre, null, meagre complement (recalled)
-- ============================================================================

/-- The Liouville numbers are comeagre (residual) in `ℝ`. -/
theorem liouville_residual : {x : ℝ | Liouville x} ∈ residual ℝ :=
  eventually_residual_liouville

/-- The Liouville numbers are Lebesgue-null. -/
theorem liouville_null : volume {x : ℝ | Liouville x} = 0 :=
  volume_setOf_liouville

/-- The non-Liouville reals are meagre (their complement `L` is comeagre). -/
theorem nonLiouville_meagre : IsMeagre {x : ℝ | Liouville x}ᶜ := by
  rw [IsMeagre, compl_compl]
  exact liouville_residual

-- ============================================================================
-- Part III: both pieces are dense
-- ============================================================================

/-- **The Liouville numbers are dense.** They are comeagre and `ℝ` is a Baire
    space, so `dense_of_mem_residual` applies. -/
theorem dense_liouville : Dense {x : ℝ | Liouville x} :=
  dense_of_mem_residual liouville_residual

/-- **The non-Liouville reals are dense — despite being meagre.** They are
    conull (`volume Lᶜᶜ = volume L = 0`), and a conull set in `ℝ` is dense by
    `dense_of_conull`. This is the sharp topological content: the *small*
    (meagre) half of the Oxtoby decomposition still meets every open interval. -/
theorem dense_nonLiouville : Dense {x : ℝ | Liouville x}ᶜ :=
  dense_of_conull (μ := volume) (by rw [compl_compl]; exact liouville_null)

-- ============================================================================
-- Part IV: ℝ as a union of two disjoint dense sets, one meagre one comeagre
-- ============================================================================

/-- **A meagre, dense set of full Lebesgue measure.** Sharpening of the
    sibling's `exists_meagre_conull`: the witness `Lᶜ` is not only meagre and
    conull but also dense. -/
theorem exists_meagre_dense_conull :
    ∃ S : Set ℝ, IsMeagre S ∧ Dense S ∧ volume Sᶜ = 0 :=
  ⟨{x : ℝ | Liouville x}ᶜ, nonLiouville_meagre, dense_nonLiouville, by
    rw [compl_compl]; exact liouville_null⟩

/-- **The dense symmetric Oxtoby decomposition.** `ℝ` partitions into two
    disjoint **dense** sets:

    * `A = L` — comeagre, null, and dense;
    * `B = Lᶜ` — meagre, conull, and dense.

    Both notions of largeness fail along this single partition (as in the
    sibling `real_symmetric_oxtoby`), and additionally *neither* failure is
    confined to a nowhere-dense set: both classes are topologically dense in
    `ℝ`. -/
theorem real_symmetric_oxtoby_dense :
    ∃ A B : Set ℝ,
      A ∪ B = univ ∧ Disjoint A B ∧ Dense A ∧ Dense B ∧
      (A ∈ residual ℝ ∧ volume A = 0) ∧
      (IsMeagre B ∧ volume Bᶜ = 0) :=
  ⟨{x : ℝ | Liouville x}, {x : ℝ | Liouville x}ᶜ,
    union_compl_self _, disjoint_compl_right,
    dense_liouville, dense_nonLiouville,
    ⟨liouville_residual, liouville_null⟩,
    ⟨nonLiouville_meagre, by rw [compl_compl]; exact liouville_null⟩⟩

#check @dense_of_conull
#check @dense_liouville
#check @dense_nonLiouville
#check @exists_meagre_dense_conull
#check @real_symmetric_oxtoby_dense

/-
  ## Results Summary

  | Theorem | Statement | Status |
  |---------|-----------|--------|
  | `dense_of_conull` | conull set is dense (IsOpenPosMeasure) | Proved |
  | `liouville_residual` | Liouville numbers comeagre | Proved (Mathlib) |
  | `liouville_null` | Liouville numbers Lebesgue-null | Proved (Mathlib) |
  | `nonLiouville_meagre` | non-Liouville reals meagre | Proved |
  | `dense_liouville` | Liouville numbers dense | Proved |
  | `dense_nonLiouville` | non-Liouville reals dense (though meagre) | Proved |
  | `exists_meagre_dense_conull` | ∃ meagre dense conull set | Proved |
  | `real_symmetric_oxtoby_dense` | ℝ = two disjoint dense sets | Proved |

  **Sorries**: 0
  **Axioms**: 0 declared (Mathlib triple inherited)
-/

end AlgebraicRealsMeagerOQ02OQ01Dense
