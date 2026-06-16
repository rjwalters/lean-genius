/-
  Erdős #1047 — OQ-02: Goodman counterexample certificate (SKELETON)

  Goal: discharge the lone remaining axiom of `Erdos1047Problem.lean`,

      axiom goodman_counterexample :
        ∃ z₀ ∈ lemniscate goodmanPolynomial goodmanCriticalValue,
          ¬ IsConvexComplex (componentContaining
              (lemniscate goodmanPolynomial goodmanCriticalValue) z₀)

  using the build-verified topological bridge
  `componentContaining_lemniscate_not_convex_of_chord_exits`
  (in `Erdos1047OQ02Reduction.lean`).  That bridge reduces non-convexity of a
  lemniscate component to a purely geometric certificate:

      a preconnected arc `C ⊆ {|f| ≤ c}` joining z₀=−i, z₁=+i whose chord
      midpoint m = 0 escapes the sublevel set (‖f(0)‖ = 4 > c = 5^{3/2}/4).

  The arc is the 4-segment polyline  −i → (1−i)/2 → 2 → (1+i)/2 → +i.

  STATUS: structural skeleton.  PROVED here (no sorry):
    • endpoint evaluations f(±i) = 0  (the `(z²+1)` factor),
    • the chord-exit estimate  c < ‖f(0)‖ = 4,
    • arc endpoint memberships  −i, +i ∈ C,
    • the full assembly into `goodman_counterexample_proof` via the bridge.
  REMAINING (two `sorry`s, fully specified in knowledge.md):
    • `goodmanArc_isPreconnected`  — `IsPreconnected.union` of 4 affine images,
    • `goodmanArc_subset_lemniscate` — the 4 segment inequalities
      ‖f(z(s))‖ ≤ c, each ⟸ normSq = Re²+Im² ⟸ D=(k/16)·SQ·P (ring) ⟸ Bernstein.

  This file is an UNREGISTERED orphan (not in `Proofs.lean`): it does NOT yet
  change the axiom count of the gallery entry.  When the two `sorry`s close and
  it builds green, a downstream restructure removes the parent axiom.
-/

import Proofs.Erdos1047OQ02Reduction
import Mathlib.Tactic

open Polynomial Set Erdos1047 Erdos1047OQ02

namespace Erdos1047OQ02Cert

/-! ## Polynomial evaluations at the key points -/

/-- `f(0) = (0²+1)(0−2)² = 4`. -/
lemma eval_zero_eq_four : goodmanPolynomial.eval 0 = 4 := by
  simp only [goodmanPolynomial, eval_mul, eval_add, eval_pow, eval_X, eval_one,
    eval_sub, eval_ofNat]
  norm_num

/-- `f(+i) = 0`: the `(z²+1)` factor vanishes at `i`. -/
lemma eval_I_zero : goodmanPolynomial.eval Complex.I = 0 := by
  simp only [goodmanPolynomial, eval_mul, eval_add, eval_pow, eval_X, eval_one,
    eval_sub, eval_ofNat]
  linear_combination ((Complex.I - 2) ^ 2) * Complex.I_sq

/-- `f(−i) = 0`: the `(z²+1)` factor vanishes at `−i`. -/
lemma eval_negI_zero : goodmanPolynomial.eval (-Complex.I) = 0 := by
  simp only [goodmanPolynomial, eval_mul, eval_add, eval_pow, eval_X, eval_one,
    eval_sub, eval_ofNat]
  linear_combination ((-Complex.I - 2) ^ 2) * Complex.I_sq

/-! ## The chord-exit estimate -/

/-- The chord midpoint `m = (1 − ½)·(−i) + ½·i = 0` escapes the lemniscate:
    `c = 5^{3/2}/4 ≈ 2.795 < 4 = ‖f(0)‖`. -/
lemma chord_exit :
    goodmanCriticalValue <
      ‖goodmanPolynomial.eval ((1 - (1/2 : ℝ)) • (-Complex.I) + (1/2 : ℝ) • Complex.I)‖ := by
  have hmid : (1 - (1/2 : ℝ)) • (-Complex.I) + (1/2 : ℝ) • Complex.I = 0 := by
    have h12 : (1 - (1/2 : ℝ)) = (1/2 : ℝ) := by norm_num
    rw [h12, smul_neg, neg_add_cancel]
  rw [hmid, eval_zero_eq_four]
  have hnorm : ‖(4 : ℂ)‖ = 4 := by simp
  rw [hnorm]
  unfold goodmanCriticalValue
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 4)]
  -- reduce to `5^(3/2) < 16` via `5^(3/2) = 5·√5` and `√5 < 3`
  have key : (5 : ℝ) ^ (3/2 : ℝ) = 5 * Real.sqrt 5 := by
    rw [Real.sqrt_eq_rpow, show (3/2 : ℝ) = 1 + 1/2 by norm_num,
      Real.rpow_add (by norm_num : (0 : ℝ) < 5), Real.rpow_one]
  rw [key]
  have h5 : Real.sqrt 5 < 3 := by
    have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 5, hsq]
  nlinarith [h5, Real.sqrt_nonneg 5]

/-! ## The 4-segment polyline arc -/

/-- An affine segment `a → b` as the image of `[0,1]` under `s ↦ (1−s)•a + s•b`. -/
noncomputable def seg (a b : ℂ) : Set ℂ :=
  (fun s : ℝ => (1 - s) • a + s • b) '' Set.Icc (0 : ℝ) 1

lemma mem_seg_left (a b : ℂ) : a ∈ seg a b :=
  ⟨0, ⟨le_refl 0, by norm_num⟩, by simp⟩

lemma mem_seg_right (a b : ℂ) : b ∈ seg a b :=
  ⟨1, ⟨by norm_num, le_refl 1⟩, by simp⟩

/-- Goodman's certificate arc: the polyline `−i → (1−i)/2 → 2 → (1+i)/2 → +i`. -/
noncomputable def goodmanArc : Set ℂ :=
  seg (-Complex.I) ((1 - Complex.I) / 2) ∪ seg ((1 - Complex.I) / 2) 2 ∪
  seg 2 ((1 + Complex.I) / 2) ∪ seg ((1 + Complex.I) / 2) Complex.I

lemma arc_mem_negI : (-Complex.I) ∈ goodmanArc := by
  unfold goodmanArc
  exact Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (mem_seg_left _ _)))

lemma arc_mem_I : Complex.I ∈ goodmanArc := by
  unfold goodmanArc
  exact Set.mem_union_right _ (mem_seg_right _ _)

/-- REMAINING OBLIGATION 1: the polyline is preconnected.
    Each `seg` is `isPreconnected_Icc.image` of a continuous affine map; the four
    are glued at the shared waypoints `(1−i)/2, 2, (1+i)/2` via `IsPreconnected.union`. -/
lemma goodmanArc_isPreconnected : IsPreconnected goodmanArc := by
  sorry

/-- REMAINING OBLIGATION 2: the polyline lies inside the lemniscate.
    Per segment `a→b`, with `z(s)=(1−s)•a+s•b`,
    `‖f(z(s))‖ ≤ c ⟸ ‖f(z(s))‖² ≤ 125/16 ⟸ normSq = Re(s)²+Im(s)²`
    ⟸ `125/16 − (Re²+Im²) = (k/16)·SQ(s)·P(s)` (ring) with `SQ ≥ 0` (`sq_nonneg`)
    and `P ≥ 0` (all-nonneg Bernstein coefficients). Tables in knowledge.md. -/
lemma goodmanArc_subset_lemniscate :
    goodmanArc ⊆ lemniscate goodmanPolynomial goodmanCriticalValue := by
  sorry

/-! ## Assembly -/

/-- `−i` lies in the lemniscate (since `f(−i)=0`). -/
lemma negI_mem_lemniscate :
    (-Complex.I) ∈ lemniscate goodmanPolynomial goodmanCriticalValue := by
  simp only [lemniscate, Set.mem_setOf_eq, eval_negI_zero, norm_zero]
  unfold goodmanCriticalValue; positivity

/-- **Goodman's counterexample, discharged from the geometric certificate.**
    Same statement as the parent file's `goodman_counterexample` axiom. -/
theorem goodman_counterexample_proof :
    ∃ z₀ ∈ lemniscate goodmanPolynomial goodmanCriticalValue,
      ¬IsConvexComplex (componentContaining
        (lemniscate goodmanPolynomial goodmanCriticalValue) z₀) :=
  ⟨-Complex.I, negI_mem_lemniscate,
    componentContaining_lemniscate_not_convex_of_chord_exits
      (C := goodmanArc) (z₁ := Complex.I) (t := 1/2)
      goodmanArc_isPreconnected goodmanArc_subset_lemniscate
      arc_mem_negI arc_mem_I (by norm_num) (by norm_num) chord_exit⟩

end Erdos1047OQ02Cert
