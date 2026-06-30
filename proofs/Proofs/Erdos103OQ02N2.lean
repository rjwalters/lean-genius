/-
Erdős Problem #103 — Open Question 02: the first non-degenerate case `n = 2`.

## What this adds over `Erdos103OQ02.lean` / `Erdos103OQ02Finite.lean`

The parent OQ-02 audit showed the raw count `h(n)` is degenerate (≡ 0 for `n ≥ 1`)
and supplied the corrected congruence count `hCong n`. The sibling `…Finite` file
discharged the open `[Finite (Quotient (OptimalSetoid n))]` hypothesis only in the
*degenerate* small cases `n ≤ 1`, where `diameter n ≡ 0` and every configuration is
optimal for trivial reasons.

This file handles the **first genuinely non-degenerate case `n = 2`**, where the
diameter is an honest distance. It proves, unconditionally and 0-axiom:

1. `diameter_two`  : for a 2-point configuration the diameter is exactly the single
   pairwise distance `pointDist (P 0) (P 1)`.
2. `minDiameter_two` : `minDiameter 2 = 1` — two points cannot be closer than the
   separation constraint, and a unit segment attains it.
3. `exists_optimal_two` : the unit segment `{(0,0),(1,0)}` is optimal.
4. `optimal_two_gap` : every optimal 2-configuration has its two points at distance
   *exactly* 1.
5. `optimal_two_congruent` : any two optimal 2-configurations are congruent — via an
   **explicit planar isometry** (complex multiplication by a unit number followed by a
   translation) that carries one unit segment onto the other.
6. Hence `Subsingleton`/`Finite (Quotient (OptimalSetoid 2))` and the exact value
   `hCong 2 = 1`, together with the strict gap `h 2 = 0 < 1 = hCong 2`.

This confirms — with proof — the parent file's unproven summary claim "h(2) = 1",
now restated for the corrected count `hCong`. It does **not** resolve the open Erdős
question (`hCong n ≥ 2` for large `n`), which concerns `n` far beyond 2.

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
-- PART N0: Elementary facts about `pointDist`
-- ============================================================

/-- `pointDist` is nonnegative (it is a square root). -/
theorem pointDist_nonneg (p q : ℝ × ℝ) : 0 ≤ pointDist p q := Real.sqrt_nonneg _

/-- A point is at distance `0` from itself. -/
theorem pointDist_self (p : ℝ × ℝ) : pointDist p p = 0 := by
  unfold pointDist
  simp

/-- `pointDist` is symmetric. -/
theorem pointDist_comm (p q : ℝ × ℝ) : pointDist p q = pointDist q p := by
  unfold pointDist
  congr 1
  ring

/-- The square of `pointDist` is the sum of squared coordinate differences. -/
theorem pointDist_sq (p q : ℝ × ℝ) :
    (pointDist p q) ^ 2 = (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 := by
  unfold pointDist
  rw [Real.sq_sqrt (by positivity)]

/-- The two endpoints of the unit segment are at distance exactly `1`. -/
theorem pointDist_seg : pointDist ((0, 0) : ℝ × ℝ) ((1, 0) : ℝ × ℝ) = 1 := by
  have h : pointDist ((0, 0) : ℝ × ℝ) ((1, 0) : ℝ × ℝ)
        = Real.sqrt (((0 : ℝ) - 1) ^ 2 + ((0 : ℝ) - 0) ^ 2) := rfl
  rw [h, show ((0 : ℝ) - 1) ^ 2 + ((0 : ℝ) - 0) ^ 2 = 1 from by norm_num, Real.sqrt_one]

/-- The unit segment endpoints, reversed, are also at distance `1`. -/
theorem pointDist_seg' : pointDist ((1, 0) : ℝ × ℝ) ((0, 0) : ℝ × ℝ) = 1 := by
  rw [pointDist_comm, pointDist_seg]

-- ============================================================
-- PART N1: The diameter of a 2-point configuration
-- ============================================================

/-- **Diameter of a pair.** For `n = 2`, the diameter (the supremum over all index
    pairs of `pointDist`) is exactly the single pairwise distance
    `pointDist (P 0) (P 1)`. -/
theorem diameter_two (P : PointConfig 2) :
    diameter 2 P = pointDist (P 0) (P 1) := by
  have key : ∀ i j : Fin 2, pointDist (P i) (P j) ≤ pointDist (P 0) (P 1) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      first
        | exact le_rfl
        | (rw [pointDist_self]; exact pointDist_nonneg _ _)
        | (rw [pointDist_comm]; exact le_rfl)
  unfold diameter
  rw [dif_pos (show (2 : ℕ) ≥ 2 from le_refl 2)]
  apply le_antisymm
  · apply ciSup_le
    intro i
    apply ciSup_le
    intro j
    exact key i j
  · have hbj : BddAbove (Set.range fun j : Fin 2 => pointDist (P 0) (P j)) :=
      Set.Finite.bddAbove (Set.finite_range _)
    have hbi : BddAbove (Set.range fun i : Fin 2 => ⨆ j, pointDist (P i) (P j)) :=
      Set.Finite.bddAbove (Set.finite_range _)
    calc pointDist (P 0) (P 1)
        ≤ ⨆ j, pointDist (P 0) (P j) := le_ciSup hbj 1
      _ ≤ ⨆ i, ⨆ j, pointDist (P i) (P j) := le_ciSup hbi 0

-- ============================================================
-- PART N2: The optimal diameter for two points is 1
-- ============================================================

/-- The explicit unit segment `{(0,0), (1,0)}`. -/
def segTwo : PointConfig 2 := ![(0, 0), (1, 0)]

@[simp] theorem segTwo_zero : segTwo 0 = (0, 0) := rfl
@[simp] theorem segTwo_one : segTwo 1 = (1, 0) := rfl

/-- The unit segment is a valid configuration (its two points are at distance 1 ≥ 1). -/
theorem segTwo_valid : IsValidConfig 2 segTwo := by
  intro i j hij
  have h2 : (segTwo i = (0, 0) ∧ segTwo j = (1, 0)) ∨
            (segTwo i = (1, 0) ∧ segTwo j = (0, 0)) := by
    fin_cases i <;> fin_cases j <;> simp_all [segTwo]
  rcases h2 with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · simp [hi, hj, pointDist_seg]
  · simp [hi, hj, pointDist_seg']

/-- The diameter of the unit segment is `1`. -/
theorem segTwo_diameter : diameter 2 segTwo = 1 := by
  rw [diameter_two, segTwo_zero, segTwo_one, pointDist_seg]

/-- **The minimum diameter for two points is exactly `1`.** Lower bound: every valid
    configuration has its two points separated by `≥ 1`, so its diameter is `≥ 1`.
    Upper bound: the unit segment attains `1`. -/
theorem minDiameter_two : minDiameter 2 = 1 := by
  haveI : Nonempty {P : PointConfig 2 // IsValidConfig 2 P} := ⟨⟨segTwo, segTwo_valid⟩⟩
  have hbddBelow :
      BddBelow (Set.range fun P : {P : PointConfig 2 // IsValidConfig 2 P} =>
        diameter 2 P.val) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨P, rfl⟩
    show (0 : ℝ) ≤ diameter 2 P.val
    rw [diameter_two]
    exact pointDist_nonneg _ _
  apply le_antisymm
  · calc minDiameter 2 ≤ diameter 2 segTwo :=
          ciInf_le hbddBelow ⟨segTwo, segTwo_valid⟩
        _ = 1 := segTwo_diameter
  · apply le_ciInf
    intro P
    rw [diameter_two]
    exact P.2 0 1 (by decide)

-- ============================================================
-- PART N3: Existence and the unit-gap characterization
-- ============================================================

/-- **An optimal 2-configuration exists**: the unit segment. -/
theorem exists_optimal_two : ∃ P, IsOptimal 2 P :=
  ⟨segTwo, segTwo_valid, by rw [segTwo_diameter, minDiameter_two]⟩

/-- **Every optimal 2-configuration realizes its two points at distance exactly 1.** -/
theorem optimal_two_gap {P : PointConfig 2} (hP : IsOptimal 2 P) :
    pointDist (P 0) (P 1) = 1 := by
  obtain ⟨_, hd⟩ := hP
  rw [diameter_two, minDiameter_two] at hd
  exact hd

/-- The squared coordinate spread of an optimal pair is `1`. -/
theorem optimal_two_normsq {P : PointConfig 2} (hP : IsOptimal 2 P) :
    ((P 1).1 - (P 0).1) ^ 2 + ((P 1).2 - (P 0).2) ^ 2 = 1 := by
  have hsq := pointDist_sq (P 0) (P 1)
  rw [optimal_two_gap hP] at hsq
  -- hsq : (1:ℝ)^2 = (P0.1 - P1.1)^2 + (P0.2 - P1.2)^2
  nlinarith [hsq]

-- ============================================================
-- PART N4: A planar isometry as complex multiplication
-- ============================================================

/-- Complex multiplication on `ℝ × ℝ`: `(a,b) * (x,y) = (ax - by, bx + ay)`. -/
def cmul (c z : ℝ × ℝ) : ℝ × ℝ := (c.1 * z.1 - c.2 * z.2, c.2 * z.1 + c.1 * z.2)

@[simp] theorem cmul_fst (c z : ℝ × ℝ) : (cmul c z).1 = c.1 * z.1 - c.2 * z.2 := rfl
@[simp] theorem cmul_snd (c z : ℝ × ℝ) : (cmul c z).2 = c.2 * z.1 + c.1 * z.2 := rfl

/-- `cmul` is additive in its second argument (it is ℝ-linear). -/
theorem cmul_sub (c z w : ℝ × ℝ) : cmul c z - cmul c w = cmul c (z - w) := by
  apply Prod.ext <;> simp [Prod.fst_sub, Prod.snd_sub] <;> ring

/-- **Multiplication by a unit number preserves `pointDist`.** If `c` lies on the unit
    circle (`c.1² + c.2² = 1`), then `z ↦ cmul c z` is an isometry. -/
theorem cmul_preserves {c : ℝ × ℝ} (hc : c.1 ^ 2 + c.2 ^ 2 = 1) (z w : ℝ × ℝ) :
    pointDist (cmul c z) (cmul c w) = pointDist z w := by
  unfold pointDist
  congr 1
  have e1 : (cmul c z).1 - (cmul c w).1 = c.1 * (z.1 - w.1) - c.2 * (z.2 - w.2) := by
    simp [cmul_fst]; ring
  have e2 : (cmul c z).2 - (cmul c w).2 = c.2 * (z.1 - w.1) + c.1 * (z.2 - w.2) := by
    simp [cmul_snd]; ring
  rw [e1, e2]
  nlinarith [hc, sq_nonneg (z.1 - w.1), sq_nonneg (z.2 - w.2)]

/-- Right-inverse identity for a unit `c`: composing `cmul c` with `cmul (conj c)`
    returns the input. (`conj c = (c.1, -c.2)`.) -/
theorem cmul_conj_left {c : ℝ × ℝ} (hc : c.1 ^ 2 + c.2 ^ 2 = 1) (z : ℝ × ℝ) :
    cmul c (cmul (c.1, -c.2) z) = z := by
  apply Prod.ext <;> simp only [cmul_fst, cmul_snd]
  · linear_combination z.1 * hc
  · linear_combination z.2 * hc

/-- Left-inverse identity for a unit `c`. -/
theorem cmul_conj_right {c : ℝ × ℝ} (hc : c.1 ^ 2 + c.2 ^ 2 = 1) (z : ℝ × ℝ) :
    cmul (c.1, -c.2) (cmul c z) = z := by
  apply Prod.ext <;> simp only [cmul_fst, cmul_snd]
  · linear_combination z.1 * hc
  · linear_combination z.2 * hc

/-- The planar isometry sending the directed unit segment `(a₀,a₁)` to `(b₀,b₁)`:
    translate `a₀` to the origin, rotate by the unit number `c`, translate to `b₀`. -/
noncomputable def segIsom (c a₀ b₀ : ℝ × ℝ) (hc : c.1 ^ 2 + c.2 ^ 2 = 1) : Isometry2D where
  toFun p := b₀ + cmul c (p - a₀)
  preserves_dist p q := by
    have h1 : pointDist (b₀ + cmul c (p - a₀)) (b₀ + cmul c (q - a₀))
            = pointDist (cmul c (p - a₀)) (cmul c (q - a₀)) := by
      rw [add_comm b₀ (cmul c (p - a₀)), add_comm b₀ (cmul c (q - a₀))]
      exact pointDist_add_right _ _ b₀
    rw [h1, cmul_preserves hc]
    have h2 : pointDist (p - a₀) (q - a₀) = pointDist p q := by
      rw [sub_eq_add_neg p a₀, sub_eq_add_neg q a₀]
      exact pointDist_add_right p q (-a₀)
    rw [h2]
  bijective := by
    refine Function.bijective_iff_has_inverse.mpr
      ⟨fun y => a₀ + cmul (c.1, -c.2) (y - b₀), ?_, ?_⟩
    · intro p
      simp only
      rw [add_sub_cancel_left, cmul_conj_right hc, add_sub_cancel]
    · intro y
      simp only
      rw [add_sub_cancel_left, cmul_conj_left hc, add_sub_cancel]

-- ============================================================
-- PART N5: All optimal 2-configurations are congruent
-- ============================================================

/-- **Uniqueness up to congruence.** Any two optimal 2-point configurations are
    congruent: both are unit segments, and the explicit isometry `segIsom` rotates and
    translates one onto the other. This is the content of "h(2) = 1". -/
theorem optimal_two_congruent {P Q : PointConfig 2}
    (hP : IsOptimal 2 P) (hQ : IsOptimal 2 Q) : AreCongruent 2 P Q := by
  -- u = P 1 - P 0, w = Q 1 - Q 0 are unit vectors
  set u : ℝ × ℝ := P 1 - P 0 with hu_def
  set w : ℝ × ℝ := Q 1 - Q 0 with hw_def
  have hu : u.1 ^ 2 + u.2 ^ 2 = 1 := by
    have := optimal_two_normsq hP
    simpa [hu_def, Prod.fst_sub, Prod.snd_sub] using this
  have hw : w.1 ^ 2 + w.2 ^ 2 = 1 := by
    have := optimal_two_normsq hQ
    simpa [hw_def, Prod.fst_sub, Prod.snd_sub] using this
  -- the unit rotation c = w * conj(u)
  set c : ℝ × ℝ := (w.1 * u.1 + w.2 * u.2, w.2 * u.1 - w.1 * u.2) with hc_def
  have hc : c.1 ^ 2 + c.2 ^ 2 = 1 := by
    have : c.1 ^ 2 + c.2 ^ 2 = (w.1 ^ 2 + w.2 ^ 2) * (u.1 ^ 2 + u.2 ^ 2) := by
      simp only [hc_def]; ring
    rw [this, hu, hw]; ring
  -- the isometry carrying P onto Q
  refine ⟨segIsom c (P 0) (Q 0) hc, ?_⟩
  intro i
  fin_cases i
  · -- Q 0 = σ (P 0)
    show Q 0 = Q 0 + cmul c (P 0 - P 0)
    rw [sub_self]
    simp [cmul]
  · -- Q 1 = σ (P 1)
    show Q 1 = Q 0 + cmul c (P 1 - P 0)
    have hcu : cmul c (P 1 - P 0) = w := by
      apply Prod.ext <;>
        simp only [cmul_fst, cmul_snd, hc_def, ← hu_def]
      · linear_combination w.1 * hu
      · linear_combination w.2 * hu
    rw [hcu, hw_def]
    abel

-- ============================================================
-- PART N6: hCong 2 = 1
-- ============================================================

/-- The optimal congruence quotient at `n = 2` is a subsingleton. -/
instance subsingleton_quotient_two : Subsingleton (Quotient (OptimalSetoid 2)) := by
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn with
  | _ P =>
    induction b using Quotient.inductionOn with
    | _ Q => exact Quotient.sound (optimal_two_congruent P.2 Q.2)

/-- **Unconditional finiteness at `n = 2`** — discharges the `[Finite …]` hypothesis of
    the parent non-degeneracy theorems at the first non-degenerate case. -/
instance finite_quotient_two : Finite (Quotient (OptimalSetoid 2)) :=
  Finite.of_subsingleton

/-- **`hCong 2 = 1`.** There is exactly one optimal 2-point configuration up to
    congruence (the unit segment) — the corrected count's value at the first
    non-degenerate case, matching the parent file's unproven "h(2) = 1". -/
theorem hCong_two_eq_one : hCong 2 = 1 := by
  have hne : Nonempty (Quotient (OptimalSetoid 2)) :=
    optimalQuotient_nonempty_of_exists 2 exists_optimal_two
  exact Nat.card_eq_one_iff_unique.mpr ⟨subsingleton_quotient_two, hne⟩

/-- **The corrected count strictly exceeds the degenerate raw count at `n = 2`.** The
    raw cardinality collapses (`h 2 = 0`, the optimal set is translation-infinite) while
    the congruence count is `1`. -/
theorem hCong_two_strictly_exceeds_raw : h 2 < hCong 2 :=
  hCong_strictly_exceeds_raw 2 (by norm_num) exists_optimal_two

end Erdos103OQ02

-- Export results
#check @Erdos103OQ02.diameter_two
#check @Erdos103OQ02.minDiameter_two
#check @Erdos103OQ02.exists_optimal_two
#check @Erdos103OQ02.optimal_two_gap
#check @Erdos103OQ02.optimal_two_congruent
#check @Erdos103OQ02.hCong_two_eq_one
#check @Erdos103OQ02.hCong_two_strictly_exceeds_raw
