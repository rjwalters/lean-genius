/-
Erdős Problem #103 — Open Question 02: the base case `n = 1`, computed exactly.

## Context

The audit in `Erdos103OQ02.lean` shows that the parent file's raw count
`h n = Nat.card {P // IsOptimal n P}` is degenerate — identically `0` for every
`n ≥ 1` — because optimality is translation-invariant, so the optimal set is
empty or infinite. The repair is the *congruence count*
`hCong n = Nat.card (Quotient (OptimalSetoid n))`, and Part 7 of that file proves
`hCong n ≥ 1` **conditionally**: it assumes both that an optimal configuration
exists *and* that there are only finitely many congruence classes.

This file discharges both hypotheses *unconditionally* in the base case `n = 1`,
turning the conditional lower bound into an exact computation:

    h 1 = 0   <   1 = hCong 1.

For a single point the picture is completely explicit:

* every configuration is valid (no distinct pair to separate) and has diameter `0`,
  so `minDiameter 1 = 0` and **every** configuration is optimal
  (`optimal_one`, `exists_optimal_one`);
* any two single-point configurations are congruent — translate one onto the other —
  so the optimal congruence quotient is a `Subsingleton` (`congruent_one`,
  `optimalQuotient_subsingleton_one`);
* hence the quotient is a nonempty subsingleton and `hCong 1 = 1` exactly
  (`hCong_one`), while the raw count is `h 1 = 0` (`Erdos103OQ02.h_eq_zero`).

The `Subsingleton` instance makes the `[Finite (Quotient (OptimalSetoid 1))]`
hypothesis of Part 7 hold automatically (`Finite.of_subsingleton`), so the
conditional results `hCong_pos_of_finite` and `hCong_strictly_exceeds_raw`
specialize to `n = 1` with no side conditions (`h_one_lt_hCong_one`).

The boundary case `n = 0` is computed too: there the index type is empty, so
`PointConfig 0` is `Unique`, the optimal set is a single point, and the raw count
is *not* degenerate — `h 0 = hCong 0 = 1` (`h_zero`, `hCong_zero`,
`h_zero_eq_hCong_zero`). This pinpoints the threshold: `h n = 0 < hCong n` is a
strictly `n ≥ 1` phenomenon, caused exactly by the translation freedom that is
absent when there are no points to translate.

This is a base-case computation, not a resolution: the Erdős question for `hCong`
remains open for large `n`.

## Axioms / Sorries
None. All results are machine-checked from Mathlib + the parent files only.
-/

import Mathlib
import Proofs.Erdos103Problem
import Proofs.Erdos103OQ02

open Erdos103
open Erdos103OQ02

namespace Erdos103OQ02SmallCases

-- ============================================================
-- The single-point case is fully explicit
-- ============================================================

/-- For one point the diameter is `0`: the `diameter` definition falls in its
    `n < 2` branch. -/
theorem diameter_one (P : PointConfig 1) : diameter 1 P = 0 := by
  unfold diameter
  rw [dif_neg (by decide : ¬ (1 : ℕ) ≥ 2)]

/-- Every single-point configuration is valid: there is no distinct pair of
    indices to separate. -/
theorem valid_one (P : PointConfig 1) : IsValidConfig 1 P := by
  haveI := Fin.subsingleton_one
  intro i j hij
  exact absurd (Subsingleton.elim i j) hij

/-- The minimum diameter over one point is `0`: the diameter is constantly `0`
    on the (nonempty) set of valid configurations. -/
theorem minDiameter_one : minDiameter 1 = 0 := by
  haveI : Nonempty {P : PointConfig 1 // IsValidConfig 1 P} :=
    ⟨⟨fun _ => (0, 0), valid_one _⟩⟩
  have hconst : minDiameter 1 = ⨅ _P : {P : PointConfig 1 // IsValidConfig 1 P}, (0 : ℝ) := by
    unfold minDiameter
    exact iInf_congr (fun P => diameter_one P.val)
  rw [hconst, ciInf_const]

/-- **Every single-point configuration is optimal.** Both its diameter and the
    minimum diameter equal `0`, and validity is automatic. -/
theorem optimal_one (P : PointConfig 1) : IsOptimal 1 P :=
  ⟨valid_one P, by rw [diameter_one, minDiameter_one]⟩

/-- An optimal single-point configuration exists (every one is optimal). -/
theorem exists_optimal_one : ∃ P : PointConfig 1, IsOptimal 1 P :=
  ⟨fun _ => (0, 0), optimal_one _⟩

/-- **Any two single-point configurations are congruent.** Translate the first
    onto the second by `Q 0 - P 0`; translation is an isometry
    (`Erdos103OQ02.translate_congruent`). -/
theorem congruent_one (P Q : PointConfig 1) : AreCongruent 1 P Q := by
  haveI := Fin.subsingleton_one
  have hv : Ptranslate (Q 0 - P 0) P = Q := by
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    show P 0 + (Q 0 - P 0) = Q 0
    abel
  have hcong := Erdos103OQ02.translate_congruent (Q 0 - P 0) P
  rwa [hv] at hcong

/-- **The optimal congruence quotient for `n = 1` is a subsingleton.** All
    single-point configurations are congruent, so they collapse to one class.
    Via `Finite.of_subsingleton` this also supplies the `Finite` instance that
    Part 7 of `Erdos103OQ02.lean` assumes. -/
instance optimalQuotient_subsingleton_one :
    Subsingleton (Quotient (OptimalSetoid 1)) :=
  ⟨fun a b => Quotient.inductionOn₂ a b fun P Q =>
    Quotient.sound (congruent_one P.val Q.val)⟩

-- ============================================================
-- The exact value of the corrected count at the base case
-- ============================================================

/-- **`hCong 1 = 1`, unconditionally.** The optimal congruence quotient is a
    nonempty subsingleton, so its cardinality is exactly `1`. This is the
    base case of the corrected count: where the raw count degenerates to
    `h 1 = 0`, the congruence count gives the expected single class. -/
theorem hCong_one : hCong 1 = 1 := by
  haveI : Nonempty (Quotient (OptimalSetoid 1)) :=
    optimalQuotient_nonempty_of_exists 1 exists_optimal_one
  unfold hCong
  exact Nat.card_unique

/-- The raw count vanishes at `n = 1` (the parent's degeneracy, specialized). -/
theorem h_one : h 1 = 0 := Erdos103OQ02.h_eq_zero 1 one_pos

/-- **The corrected count strictly exceeds the raw count at the base case,
    with no hypotheses:** `h 1 = 0 < 1 = hCong 1`. This is the unconditional
    instance of `Erdos103OQ02.hCong_strictly_exceeds_raw`; the `Finite` and
    existence side conditions are both discharged here. -/
theorem h_one_lt_hCong_one : h 1 < hCong 1 := by
  rw [h_one, hCong_one]; omega

-- ============================================================
-- The boundary case `n = 0`: where the degeneracy does NOT yet occur
-- ============================================================

/-
For `n = 0` there is **no** translation freedom: `PointConfig 0 = Fin 0 → ℝ × ℝ`
has a *unique* element (it is a function out of the empty type), so the optimal
set is a single point and the raw count is well-behaved: `h 0 = 1`. The
congruence count agrees, `hCong 0 = 1`. This pinpoints the threshold — the raw
count `h` only collapses to `0` once `n ≥ 1`, exactly when translation starts to
produce infinitely many distinct optimal configurations.
-/

/-- For zero points the diameter is `0` (the `n < 2` branch again). -/
theorem diameter_zero (P : PointConfig 0) : diameter 0 P = 0 := by
  unfold diameter
  rw [dif_neg (by decide : ¬ (0 : ℕ) ≥ 2)]

/-- Every zero-point configuration is valid: there are no indices at all. -/
theorem valid_zero (P : PointConfig 0) : IsValidConfig 0 P := by
  intro i
  exact i.elim0

/-- The minimum diameter over zero points is `0`. -/
theorem minDiameter_zero : minDiameter 0 = 0 := by
  haveI : Nonempty {P : PointConfig 0 // IsValidConfig 0 P} :=
    ⟨⟨default, valid_zero _⟩⟩
  have hconst : minDiameter 0 = ⨅ _P : {P : PointConfig 0 // IsValidConfig 0 P}, (0 : ℝ) := by
    unfold minDiameter
    exact iInf_congr (fun P => diameter_zero P.val)
  rw [hconst, ciInf_const]

/-- Every zero-point configuration is optimal. -/
theorem optimal_zero (P : PointConfig 0) : IsOptimal 0 P :=
  ⟨valid_zero P, by rw [diameter_zero, minDiameter_zero]⟩

/-- **The raw count is non-degenerate at `n = 0`: `h 0 = 1`.** Unlike every
    `n ≥ 1`, the optimal subtype is a nonempty subsingleton (`PointConfig 0` is
    `Unique`), so its cardinality is exactly `1`. -/
theorem h_zero : h 0 = 1 := by
  haveI : Nonempty {P : PointConfig 0 // IsOptimal 0 P} :=
    ⟨⟨default, optimal_zero _⟩⟩
  unfold h
  exact Nat.card_unique

/-- Any two zero-point configurations are congruent — indeed equal. -/
theorem congruent_zero (P Q : PointConfig 0) : AreCongruent 0 P Q := by
  have hPQ : P = Q := Subsingleton.elim P Q
  rw [← hPQ]
  exact congruent_refl 0 P

/-- The optimal congruence quotient for `n = 0` is a subsingleton. -/
instance optimalQuotient_subsingleton_zero :
    Subsingleton (Quotient (OptimalSetoid 0)) :=
  ⟨fun a b => Quotient.inductionOn₂ a b fun P Q =>
    Quotient.sound (congruent_zero P.val Q.val)⟩

/-- **`hCong 0 = 1`.** -/
theorem hCong_zero : hCong 0 = 1 := by
  haveI : Nonempty (Quotient (OptimalSetoid 0)) :=
    optimalQuotient_nonempty_of_exists 0 ⟨default, optimal_zero _⟩
  unfold hCong
  exact Nat.card_unique

/-- **At the boundary `n = 0` the two counts agree:** `h 0 = hCong 0 = 1`. The
    degeneracy `h n = 0 < hCong n` is therefore a strictly `n ≥ 1` phenomenon —
    it is precisely the translation freedom, absent when the index type is empty,
    that breaks the raw count. -/
theorem h_zero_eq_hCong_zero : h 0 = hCong 0 := by
  rw [h_zero, hCong_zero]

end Erdos103OQ02SmallCases

-- Export main results
#check @Erdos103OQ02SmallCases.optimal_one
#check @Erdos103OQ02SmallCases.exists_optimal_one
#check @Erdos103OQ02SmallCases.congruent_one
#check @Erdos103OQ02SmallCases.hCong_one
#check @Erdos103OQ02SmallCases.h_one_lt_hCong_one
#check @Erdos103OQ02SmallCases.h_zero
#check @Erdos103OQ02SmallCases.hCong_zero
#check @Erdos103OQ02SmallCases.h_zero_eq_hCong_zero
