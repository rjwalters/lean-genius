/-
Erdős Problem #103 — Open Question 02
Is h(n) ≥ 2 for all sufficiently large n?

## Open Question
OQ-02 (the "WeakConjecture" of the parent file): even the weaker statement that
there exist *two* incongruent optimal configurations for every large n is unknown.

## What This File Actually Establishes (a formalization audit)

The parent file `Erdos103Problem.lean` defines

    h (n) := Nat.card {P : PointConfig n // IsOptimal n P}

and states `WeakConjecture := ∃ N, ∀ n ≥ N, h n ≥ 2`. **As literally written, this
`h` does NOT count incongruent optimal configurations** — it counts *all* optimal
configurations, with no quotient by congruence. Because optimality is invariant
under the continuous group of translations of ℝ², the optimal set is either empty
or infinite, so `Nat.card` of it is `0` for every `n ≥ 1`.

Consequently the parent's literal `WeakConjecture` (and even the assertion
`h n ≥ 1`) is **false** under its own definitions. This file:

1. Proves translation is an isometry preserving `IsOptimal` (`translate_optimal`).
2. Proves the optimal subtype is infinite whenever it is nonempty
   (`optimal_subtype_infinite_of_nonempty`).
3. Proves the raw count is degenerate: `h n = 0` for all `n ≥ 1` (`h_eq_zero`).
4. Concludes the parent's literal `WeakConjecture` is false
   (`raw_weak_conjecture_false`).
5. Supplies the **corrected** count `hCong n`, the number of *congruence classes*
   of optimal configurations (the quantity Erdős actually asks about), and restates
   the weak conjecture against it (`WeakConjectureCorrect`).
6. Shows the corrected quotient collapses exactly the translation-infinitude that
   breaks the raw count: all translates of a configuration share one class
   (`translates_same_class`).
7. Proves the structural backbone the quotient rests on: **optimality is a full
   congruence invariant** (`optimal_of_congruent`), via the fact that every
   isometry — not just translations — preserves diameter, validity, and hence
   optimality (`isometry_diameter`, `isometry_valid`, `applyIsometry_optimal`).
   The translation results of Parts 1–3 are recovered as the
   `translationIsometry` special case (`translate_optimal_via_isometry`).
7. Proves the correction is **non-degenerate where the raw count failed**: given an
   optimal configuration and finitely many congruence classes, `hCong n ≥ 1`
   (`hCong_pos_of_finite`) and indeed `h n < hCong n` (`hCong_strictly_exceeds_raw`).
   The only way `hCong` could still vanish is the quotient being infinite — never
   empty — so the finiteness in the open question is exactly what makes the
   corrected count well-behaved.

This does **not** resolve the open Erdős question (which remains open for `hCong`);
it corrects the formalization so that the open question is stated about the right
object.

## Axioms / Sorries
None. All results are machine-checked from Mathlib + the parent file only.
-/

import Mathlib
import Proofs.Erdos103Problem

open Metric Set Finset
open Erdos103

namespace Erdos103OQ02

-- ============================================================
-- PART 1: Translation as a distance-preserving map
-- ============================================================

/-- Translation of a single point by a vector `v`. -/
def Ptranslate {n : ℕ} (v : ℝ × ℝ) (P : PointConfig n) : PointConfig n :=
  fun i => P i + v

/-- `pointDist` is translation-invariant: differences cancel the shift. -/
theorem pointDist_add_right (p q v : ℝ × ℝ) :
    pointDist (p + v) (q + v) = pointDist p q := by
  unfold pointDist
  congr 1
  simp only [Prod.fst_add, Prod.snd_add]
  ring

-- ============================================================
-- PART 2: Translation preserves optimality
-- ============================================================

/-- Translation preserves the diameter of a configuration. -/
theorem translate_diameter {n : ℕ} (v : ℝ × ℝ) (P : PointConfig n) :
    diameter n (Ptranslate v P) = diameter n P := by
  unfold diameter
  by_cases hn : n ≥ 2
  · rw [dif_pos hn, dif_pos hn]
    apply iSup_congr; intro i
    apply iSup_congr; intro j
    show pointDist (P i + v) (P j + v) = pointDist (P i) (P j)
    exact pointDist_add_right (P i) (P j) v
  · rw [dif_neg hn, dif_neg hn]

/-- Translation preserves validity (minimum separation). -/
theorem translate_valid {n : ℕ} (v : ℝ × ℝ) (P : PointConfig n)
    (hP : IsValidConfig n P) : IsValidConfig n (Ptranslate v P) := by
  intro i j hij
  show pointDist (P i + v) (P j + v) ≥ 1
  rw [pointDist_add_right]
  exact hP i j hij

/-- **Translation preserves optimality.** Since translation preserves both the
    minimum-separation constraint and the diameter, an optimal configuration is
    carried to an optimal configuration. -/
theorem translate_optimal {n : ℕ} (v : ℝ × ℝ) (P : PointConfig n)
    (hP : IsOptimal n P) : IsOptimal n (Ptranslate v P) := by
  obtain ⟨hvalid, hdiam⟩ := hP
  refine ⟨translate_valid v P hvalid, ?_⟩
  rw [translate_diameter]
  exact hdiam

-- ============================================================
-- PART 3: The optimal set is infinite when nonempty
-- ============================================================

/-- **Infinitude of the optimal set.** For `n ≥ 1`, if even one optimal
    configuration exists, then there are infinitely many: the horizontal
    translates `P₀(· ) + (t,0)` for `t : ℝ` are pairwise distinct and all optimal. -/
theorem optimal_subtype_infinite_of_nonempty (n : ℕ) (hn : 0 < n)
    (hne : ∃ P, IsOptimal n P) :
    Infinite {P : PointConfig n // IsOptimal n P} := by
  obtain ⟨P₀, hP₀⟩ := hne
  have hinj : Function.Injective
      (fun t : ℝ =>
        (⟨Ptranslate (t, 0) P₀, translate_optimal (t, 0) P₀ hP₀⟩ :
          {P : PointConfig n // IsOptimal n P})) := by
    intro s t hst
    have hval : Ptranslate (s, 0) P₀ = Ptranslate (t, 0) P₀ := congrArg Subtype.val hst
    have h0 := congrFun hval ⟨0, hn⟩
    -- h0 : P₀ ⟨0,_⟩ + (s,0) = P₀ ⟨0,_⟩ + (t,0)
    have hpair : ((s, 0) : ℝ × ℝ) = (t, 0) := (add_right_inj (P₀ ⟨0, hn⟩)).mp h0
    exact (Prod.ext_iff.mp hpair).1
  exact Infinite.of_injective _ hinj

-- ============================================================
-- PART 4: The raw count h(n) is degenerate (≡ 0)
-- ============================================================

/-- **The parent's raw count is identically zero for `n ≥ 1`.**
    Either no optimal configuration exists (the subtype is empty) or one does
    (the subtype is infinite by Part 3). In both cases `Nat.card = 0`. Hence the
    literal `h` defined in the parent file fails to count incongruent
    configurations — it is the constant `0`. -/
theorem h_eq_zero (n : ℕ) (hn : 0 < n) : h n = 0 := by
  have hh : h n = Nat.card {P : PointConfig n // IsOptimal n P} := rfl
  rw [hh, Nat.card_eq_zero]
  by_cases hne : Nonempty {P : PointConfig n // IsOptimal n P}
  · right
    obtain ⟨⟨P₀, hP₀⟩⟩ := hne
    exact optimal_subtype_infinite_of_nonempty n hn ⟨P₀, hP₀⟩
  · left
    exact not_nonempty_iff.mp hne

/-- **The parent's literal `WeakConjecture` is false.** Because `h n = 0` for every
    `n ≥ 1`, no threshold `N` can satisfy `∀ n ≥ N, h n ≥ 2`. This is exactly why
    the open question must be stated against the *congruence count* `hCong` below,
    not the raw cardinality. -/
theorem raw_weak_conjecture_false : ¬ Erdos103.WeakConjecture := by
  rintro ⟨N, hN⟩
  have hge : h (max N 1) ≥ 2 := hN (max N 1) (le_max_left _ _)
  have hpos : 0 < max N 1 := lt_of_lt_of_le Nat.one_pos (le_max_right _ _)
  rw [h_eq_zero (max N 1) hpos] at hge
  omega

-- ============================================================
-- PART 5: The corrected count — congruence classes
-- ============================================================

/-- Congruence as an equivalence relation on the *optimal* configurations.
    This is the setoid whose classes Erdős's `h(n)` is meant to count. -/
def OptimalSetoid (n : ℕ) : Setoid {P : PointConfig n // IsOptimal n P} where
  r P Q := AreCongruent n P.val Q.val
  iseqv :=
    ⟨fun P => congruent_refl n P.val,
     fun h => congruent_symm n _ _ h,
     fun h₁ h₂ => congruent_trans n _ _ _ h₁ h₂⟩

/-- **The corrected count.** `hCong n` is the number of incongruent optimal
    configurations — the cardinality of the quotient of the optimal set by
    congruence. This is the quantity in Erdős Problem #103, in contrast to the
    degenerate raw cardinality `h n`. -/
noncomputable def hCong (n : ℕ) : ℕ := Nat.card (Quotient (OptimalSetoid n))

/-- The weak conjecture, correctly stated against the congruence count. -/
def WeakConjectureCorrect : Prop := ∃ N : ℕ, ∀ n ≥ N, hCong n ≥ 2

/-- Any configuration is congruent to each of its translates (translation is an
    isometry). -/
theorem translate_congruent {n : ℕ} (v : ℝ × ℝ) (P : PointConfig n) :
    AreCongruent n P (Ptranslate v P) := by
  refine ⟨⟨fun p => p + v, fun p q => pointDist_add_right p q v,
    (Equiv.addRight v).bijective⟩, ?_⟩
  intro i; rfl

/-- **The quotient collapses the translation-infinitude.** All horizontal (indeed
    arbitrary) translates of a fixed optimal configuration map to the *same* class
    of `hCong`. This is precisely why `hCong` is finite/meaningful where the raw
    count `h` collapsed to `0`: the infinitely many translates that killed the raw
    cardinality are a single congruence class. -/
theorem translates_same_class {n : ℕ} (v : ℝ × ℝ)
    (P : {P : PointConfig n // IsOptimal n P}) :
    (Quotient.mk (OptimalSetoid n) P) =
      Quotient.mk (OptimalSetoid n)
        ⟨Ptranslate v P.val, translate_optimal v P.val P.2⟩ :=
  Quotient.sound (translate_congruent v P.val)

-- ============================================================
-- PART 6: Logical relationships of the corrected conjectures
-- ============================================================

/-- The corrected weak conjecture follows from the (corrected) main conjecture
    `∀ C, ∃ N, ∀ n ≥ N, hCong n > C`. -/
theorem correct_main_implies_weak
    (hmain : ∀ C : ℕ, ∃ N : ℕ, ∀ n ≥ N, hCong n > C) :
    WeakConjectureCorrect := by
  obtain ⟨N, hN⟩ := hmain 1
  exact ⟨N, fun n hn => hN n hn⟩

-- ============================================================
-- PART 7: The correction is non-degenerate where the raw count failed
-- ============================================================

/-- The optimal congruence-class quotient is **nonempty** whenever any optimal
    configuration exists — the class of that configuration witnesses it. This is
    the first half of the contrast with the raw count: emptiness is never the
    reason `hCong` could vanish. -/
theorem optimalQuotient_nonempty_of_exists (n : ℕ) (hne : ∃ P, IsOptimal n P) :
    Nonempty (Quotient (OptimalSetoid n)) := by
  obtain ⟨P, hP⟩ := hne
  exact ⟨Quotient.mk (OptimalSetoid n) ⟨P, hP⟩⟩

/-- **The corrected count is non-degenerate.** Whenever an optimal configuration
    exists *and there are only finitely many congruence classes*, `hCong n ≥ 1`.
    Contrast this with `h_eq_zero`, where the raw count is unconditionally `0`:
    the only thing that can drag `Nat.card (Quotient …)` down to `0` is the
    quotient being infinite, never empty. The finiteness hypothesis is exactly the
    content the open Erdős question is about — *given* it, the congruence count
    behaves, which is precisely why it, and not the raw cardinality, is the right
    object. -/
theorem hCong_pos_of_finite (n : ℕ) [Finite (Quotient (OptimalSetoid n))]
    (hne : ∃ P, IsOptimal n P) : 1 ≤ hCong n := by
  have : Nonempty (Quotient (OptimalSetoid n)) :=
    optimalQuotient_nonempty_of_exists n hne
  exact Nat.card_pos

/-- **The correction strictly exceeds the raw count where it matters.** For `n ≥ 1`
    with an optimal configuration present and finitely many congruence classes, the
    corrected count is *strictly larger* than the degenerate raw count:
    `h n = 0 < 1 ≤ hCong n`. This is the precise sense in which moving from `h` to
    `hCong` repairs the formalization: the infinitely many translates that forced
    `h n = 0` collapse to congruence classes that `hCong` actually counts. -/
theorem hCong_strictly_exceeds_raw (n : ℕ) (hn : 0 < n)
    [Finite (Quotient (OptimalSetoid n))] (hne : ∃ P, IsOptimal n P) :
    h n < hCong n := by
  rw [h_eq_zero n hn]
  exact hCong_pos_of_finite n hne

-- ============================================================
-- PART 8: Optimality is a full congruence invariant
-- ============================================================

/-- **Any isometry preserves the diameter** of a configuration. This generalizes
    `translate_diameter` (Part 2) from the translation subgroup to the entire
    isometry group `Isometry2D` used to define congruence. -/
theorem isometry_diameter {n : ℕ} (σ : Isometry2D) (P : PointConfig n) :
    diameter n (applyIsometry n σ P) = diameter n P := by
  unfold diameter
  by_cases hn : n ≥ 2
  · rw [dif_pos hn, dif_pos hn]
    apply iSup_congr; intro i
    apply iSup_congr; intro j
    show pointDist (σ.toFun (P i)) (σ.toFun (P j)) = pointDist (P i) (P j)
    exact σ.preserves_dist (P i) (P j)
  · rw [dif_neg hn, dif_neg hn]

/-- **Any isometry preserves validity** (the minimum-separation constraint).
    Generalizes `translate_valid` (Part 2) to the full isometry group. -/
theorem isometry_valid {n : ℕ} (σ : Isometry2D) (P : PointConfig n)
    (hP : IsValidConfig n P) : IsValidConfig n (applyIsometry n σ P) := by
  intro i j hij
  show pointDist (σ.toFun (P i)) (σ.toFun (P j)) ≥ 1
  rw [σ.preserves_dist]
  exact hP i j hij

/-- **Any isometry preserves optimality.** The full-group generalization of
    `translate_optimal` (Part 2): translation is just one isometry, so the
    translation infinitude of Part 3 is a single slice of this invariance. -/
theorem applyIsometry_optimal {n : ℕ} (σ : Isometry2D) (P : PointConfig n)
    (hP : IsOptimal n P) : IsOptimal n (applyIsometry n σ P) := by
  obtain ⟨hvalid, hdiam⟩ := hP
  refine ⟨isometry_valid σ P hvalid, ?_⟩
  rw [isometry_diameter]
  exact hdiam

/-- **Optimality is a congruence invariant.** If `P` is optimal and `Q` is
    congruent to `P`, then `Q` is optimal too. This is the structural backbone of
    `hCong`: the congruence quotient of the *optimal* subtype is well-posed
    precisely because being optimal is constant on each congruence class. Without
    this fact, "incongruent optimal configurations" would not even be well-defined
    as a quotient of optimal configurations. -/
theorem optimal_of_congruent {n : ℕ} (P Q : PointConfig n)
    (hP : IsOptimal n P) (hcong : AreCongruent n P Q) : IsOptimal n Q := by
  obtain ⟨σ, hσ⟩ := hcong
  have hQ : Q = applyIsometry n σ P := funext hσ
  rw [hQ]
  exact applyIsometry_optimal σ P hP

/-- Translation by `v`, packaged as an element of the isometry group. -/
def translationIsometry (v : ℝ × ℝ) : Isometry2D where
  toFun := fun p => p + v
  preserves_dist := fun p q => pointDist_add_right p q v
  bijective := (Equiv.addRight v).bijective

/-- The translation results of Parts 1–3 are exactly the `translationIsometry v`
    instances of the isometry invariance of Part 8: `Ptranslate v` is the
    application of the corresponding isometry. -/
theorem Ptranslate_eq_applyIsometry {n : ℕ} (v : ℝ × ℝ) (P : PointConfig n) :
    Ptranslate v P = applyIsometry n (translationIsometry v) P := rfl

/-- `translate_optimal` (Part 2) recovered as the translation special case of the
    full-group `applyIsometry_optimal`, confirming the generalization subsumes the
    earlier translation-only result. -/
theorem translate_optimal_via_isometry {n : ℕ} (v : ℝ × ℝ) (P : PointConfig n)
    (hP : IsOptimal n P) : IsOptimal n (Ptranslate v P) := by
  rw [Ptranslate_eq_applyIsometry]
  exact applyIsometry_optimal (translationIsometry v) P hP

end Erdos103OQ02

-- Export main results
#check @Erdos103OQ02.translate_optimal
#check @Erdos103OQ02.optimal_subtype_infinite_of_nonempty
#check @Erdos103OQ02.h_eq_zero
#check @Erdos103OQ02.raw_weak_conjecture_false
#check @Erdos103OQ02.hCong
#check @Erdos103OQ02.translates_same_class
#check @Erdos103OQ02.hCong_pos_of_finite
#check @Erdos103OQ02.hCong_strictly_exceeds_raw
#check @Erdos103OQ02.isometry_diameter
#check @Erdos103OQ02.applyIsometry_optimal
#check @Erdos103OQ02.optimal_of_congruent
#check @Erdos103OQ02.translate_optimal_via_isometry
