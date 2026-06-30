/-
Erdős Problem #103 — Open Question 02: unconditional finiteness in the
degenerate small cases (n ≤ 1).

## What this adds over `Erdos103OQ02.lean`

The non-degeneracy results in the parent OQ-02 file
(`hCong_pos_of_finite`, `hCong_strictly_exceeds_raw`) carry the typeclass
hypothesis `[Finite (Quotient (OptimalSetoid n))]`. Unconditional finiteness of
that quotient for *general* n is exactly the open content of the problem and
remains open. This file discharges the hypothesis **unconditionally for n ≤ 1**:

* n = 0: `PointConfig 0 = Fin 0 → ℝ²` has a unique element, so any two
  configurations are equal, hence congruent.
* n = 1: any two single-point configurations differ by the translation
  `Q 0 - P 0`, which is an isometry, so they are congruent.

In either case every pair of optimal configurations is congruent, so the optimal
quotient is a `Subsingleton`, hence `Finite`. Supplying these instances turns the
conditional parent theorems into unconditional statements at n = 0, 1, and lets
us compute `hCong 0 = hCong 1 = 1` together with the strict gap `h 1 < hCong 1`.

This does **not** touch the open question (unconditional finiteness for large n,
and `hCong n ≥ 2`); it only nails down the base cases that the conditional
machinery left implicit.

## Axioms / Sorries
None. Machine-checked from Mathlib + `Erdos103Problem` + `Erdos103OQ02`.
-/

import Mathlib
import Proofs.Erdos103Problem
import Proofs.Erdos103OQ02

open Metric Set Finset
open Erdos103

namespace Erdos103OQ02

-- ============================================================
-- PART F1: Every configuration is congruent in the small cases
-- ============================================================

/-- For `n = 0` there is exactly one configuration (the empty tuple), so any two
    configurations are equal and therefore congruent. -/
theorem all_congruent_zero (P Q : PointConfig 0) : AreCongruent 0 P Q := by
  have hPQ : P = Q := Subsingleton.elim P Q
  rw [hPQ]
  exact congruent_refl 0 Q

/-- For `n = 1` any two single-point configurations differ by the translation
    `Q 0 - P 0`, which is an isometry; hence they are congruent. -/
theorem all_congruent_one (P Q : PointConfig 1) : AreCongruent 1 P Q := by
  have hv : Ptranslate (Q 0 - P 0) P = Q := by
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    show P 0 + (Q 0 - P 0) = Q 0
    abel
  rw [← hv]
  exact translate_congruent (Q 0 - P 0) P

-- ============================================================
-- PART F2: The optimal quotient is a subsingleton, hence finite
-- ============================================================

/-- The optimal congruence quotient at `n = 0` is a subsingleton: all optimal
    configurations are congruent. -/
instance subsingleton_quotient_zero : Subsingleton (Quotient (OptimalSetoid 0)) := by
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn with
  | _ P =>
    induction b using Quotient.inductionOn with
    | _ Q => exact Quotient.sound (all_congruent_zero P.val Q.val)

/-- The optimal congruence quotient at `n = 1` is a subsingleton. -/
instance subsingleton_quotient_one : Subsingleton (Quotient (OptimalSetoid 1)) := by
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn with
  | _ P =>
    induction b using Quotient.inductionOn with
    | _ Q => exact Quotient.sound (all_congruent_one P.val Q.val)

/-- **Unconditional finiteness at `n = 0`** — discharges the `[Finite …]`
    hypothesis of the parent file's non-degeneracy theorems. -/
instance finite_quotient_zero : Finite (Quotient (OptimalSetoid 0)) :=
  Finite.of_subsingleton

/-- **Unconditional finiteness at `n = 1`**. -/
instance finite_quotient_one : Finite (Quotient (OptimalSetoid 1)) :=
  Finite.of_subsingleton

-- ============================================================
-- PART F3: Existence of an optimal configuration for n ≤ 1
-- ============================================================

/-- The diameter is identically `0` below the `n ≥ 2` threshold. -/
theorem diameter_eq_zero_of_lt_two {n : ℕ} (hn : ¬ 2 ≤ n) (P : PointConfig n) :
    diameter n P = 0 := by
  unfold diameter
  rw [dif_neg hn]

/-- A single point (the constant-zero configuration) is valid for `n ≤ 1`: the
    minimum-separation constraint is vacuous because distinct indices do not
    exist. -/
theorem valid_const_zero {n : ℕ} (hn : n ≤ 1) :
    IsValidConfig n (fun _ : Fin n => (0, 0)) := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  exact absurd (Fin.ext (by omega : (i : ℕ) = j)) hij

/-- For `n ≤ 1` the minimum diameter is `0`: every valid configuration has
    diameter `0`, and at least one valid configuration exists. -/
theorem minDiameter_eq_zero_of_le_one {n : ℕ} (hn : n ≤ 1) : minDiameter n = 0 := by
  have hlt : ¬ 2 ≤ n := by omega
  have hne : Nonempty {P : PointConfig n // IsValidConfig n P} :=
    ⟨⟨fun _ => (0, 0), valid_const_zero hn⟩⟩
  unfold minDiameter
  have hconst : ∀ P : {P : PointConfig n // IsValidConfig n P},
      diameter n P.val = 0 := fun P => diameter_eq_zero_of_lt_two hlt P.val
  rw [iInf_congr hconst]
  exact ciInf_const

/-- **Existence of an optimal configuration for `n ≤ 1`.** The constant-zero
    configuration is valid and has diameter `0 = minDiameter n`. -/
theorem exists_optimal_of_le_one {n : ℕ} (hn : n ≤ 1) : ∃ P, IsOptimal n P := by
  refine ⟨fun _ => (0, 0), valid_const_zero hn, ?_⟩
  rw [diameter_eq_zero_of_lt_two (by omega), minDiameter_eq_zero_of_le_one hn]

-- ============================================================
-- PART F4: Unconditional values of hCong at n = 0, 1
-- ============================================================

/-- **`hCong 0 = 1`, unconditionally.** The optimal quotient at `n = 0` is a
    nonempty subsingleton. -/
theorem hCong_zero_eq_one : hCong 0 = 1 := by
  have hne : Nonempty (Quotient (OptimalSetoid 0)) :=
    optimalQuotient_nonempty_of_exists 0 (exists_optimal_of_le_one (by norm_num))
  have hcard : Nat.card (Quotient (OptimalSetoid 0)) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨subsingleton_quotient_zero, hne⟩
  exact hcard

/-- **`hCong 1 = 1`, unconditionally.** -/
theorem hCong_one_eq_one : hCong 1 = 1 := by
  have hne : Nonempty (Quotient (OptimalSetoid 1)) :=
    optimalQuotient_nonempty_of_exists 1 (exists_optimal_of_le_one (le_refl 1))
  have hcard : Nat.card (Quotient (OptimalSetoid 1)) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨subsingleton_quotient_one, hne⟩
  exact hcard

/-- **The corrected count strictly exceeds the raw count at `n = 1`,
    unconditionally.** At `n = 1` the raw cardinality collapses (`h 1 = 0`, the
    optimal set is translation-infinite) while the congruence count is `1`. This
    is the parent theorem `hCong_strictly_exceeds_raw` with its `[Finite …]`
    hypothesis now discharged. -/
theorem hCong_one_strictly_exceeds_raw : h 1 < hCong 1 :=
  hCong_strictly_exceeds_raw 1 (by norm_num) (exists_optimal_of_le_one (le_refl 1))

end Erdos103OQ02

-- Export results
#check @Erdos103OQ02.all_congruent_zero
#check @Erdos103OQ02.all_congruent_one
#check @Erdos103OQ02.finite_quotient_zero
#check @Erdos103OQ02.finite_quotient_one
#check @Erdos103OQ02.exists_optimal_of_le_one
#check @Erdos103OQ02.hCong_zero_eq_one
#check @Erdos103OQ02.hCong_one_eq_one
#check @Erdos103OQ02.hCong_one_strictly_exceeds_raw
