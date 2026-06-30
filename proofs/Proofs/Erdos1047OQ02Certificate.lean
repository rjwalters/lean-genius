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

  STATUS: COMPLETE — no `sorry`.  Build-verified.  PROVED here:
    • endpoint evaluations f(±i) = 0  (the `(z²+1)` factor),
    • the chord-exit estimate  c < ‖f(0)‖ = 4,
    • arc endpoint memberships  −i, +i ∈ C,
    • `goodmanArc_isPreconnected`  — `IsPreconnected.union` of 4 affine images,
    • `goodmanArc_subset_lemniscate` — the 4 segment inequalities
      ‖f(z(s))‖ ≤ c, each ⟸ normSq = Re²+Im² ⟸ D=(k/16)·SQ·P (ring) ⟸ Bernstein,
    • the full assembly into `goodman_counterexample_proof` via the bridge.

  `goodman_counterexample_proof` now has the EXACT statement of the parent file's
  `goodman_counterexample` axiom, proved with no `sorry` and no new axioms — so the
  parent axiom is mathematically discharged.  This file remains an UNREGISTERED
  orphan (not in `Proofs.lean`); removing the parent `axiom` itself needs a
  downstream restructure (the parent cannot import this certificate — circular).
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

/-- Each affine segment is preconnected: continuous image of `Icc 0 1`. -/
lemma seg_isPreconnected (a b : ℂ) : IsPreconnected (seg a b) := by
  apply isPreconnected_Icc.image
  apply Continuous.continuousOn
  fun_prop

/-- The polyline is preconnected: the four segments are glued at the shared
    waypoints `(1−i)/2, 2, (1+i)/2` via `IsPreconnected.union`. -/
lemma goodmanArc_isPreconnected : IsPreconnected goodmanArc := by
  have hA := seg_isPreconnected (-Complex.I) ((1 - Complex.I) / 2)
  have hB := seg_isPreconnected ((1 - Complex.I) / 2) 2
  have hC := seg_isPreconnected 2 ((1 + Complex.I) / 2)
  have hD := seg_isPreconnected ((1 + Complex.I) / 2) Complex.I
  have hAB := hA.union ((1 - Complex.I) / 2) (mem_seg_right _ _) (mem_seg_left _ _) hB
  have hABC := hAB.union (2 : ℂ) (Or.inr (mem_seg_right _ _)) (mem_seg_left _ _) hC
  exact hABC.union ((1 + Complex.I) / 2) (Or.inr (mem_seg_right _ _)) (mem_seg_left _ _) hD

/-! ## The 4 segment membership inequalities

  Each segment `a→b` lies inside `{‖f‖ ≤ c}`.  The discharge is a uniform,
  search-free certificate (`research/problems/erdos-1047-oq-02/`):

      ‖f(z(s))‖ ≤ c  ⟸  ‖f(z(s))‖² ≤ 125/16  (`c² = 125/16`)
                     ⟸  normSq = Re(s)² + Im(s)²   (`Complex.normSq_apply`)
                     ⟸  125/16 − (Re²+Im²) = (k/16)·SQ(s)·P(s)   (a `ring` identity)

  with `SQ ∈ {s², (1−s)²}` a perfect square and `P` a degree-6 cofactor that is
  positive on `[0,1]` because it has **all-nonnegative Bernstein coefficients**.
  So `(k/16)·SQ·P` is a nonnegative ℚ-combination of the monomials
  `sʲ(1−s)^(8−j)`, and `nlinarith` closes each inequality from the products
  `mul_nonneg (pow_nonneg hs0 j) (pow_nonneg h1s (8−j))` (`j = 0…8`) — the same
  hint list works for every segment.  Sympy-verified
  (`chord_exits_sos_certificate.py`, all identities `True`). -/

/-- `c² = 125/16` (lets the segment work stay over ℚ, avoiding `rpow`). -/
lemma cval_sq : goodmanCriticalValue ^ 2 = 125 / 16 := by
  unfold goodmanCriticalValue
  have key : (5 : ℝ) ^ (3 / 2 : ℝ) = 5 * Real.sqrt 5 := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (by norm_num : (0 : ℝ) < 5), Real.rpow_one]
  rw [key, div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  norm_num

/-- Reduce membership `z ∈ {‖f‖ ≤ c}` to the rational squared bound `normSq ≤ 125/16`. -/
lemma mem_lemniscate_of_normSq_le {z : ℂ}
    (h : Complex.normSq (goodmanPolynomial.eval z) ≤ 125 / 16) :
    z ∈ lemniscate goodmanPolynomial goodmanCriticalValue := by
  simp only [lemniscate, Set.mem_setOf_eq]
  have hc0 : (0 : ℝ) ≤ goodmanCriticalValue := by unfold goodmanCriticalValue; positivity
  nlinarith [Complex.sq_norm (goodmanPolynomial.eval z), h, cval_sq,
    norm_nonneg (goodmanPolynomial.eval z), hc0]

/-- Segment 1: `−i → (1−i)/2 ⊆ {‖f‖ ≤ c}`. -/
lemma seg1_subset :
    seg (-Complex.I) ((1 - Complex.I) / 2) ⊆
      lemniscate goodmanPolynomial goodmanCriticalValue := by
  simp only [seg]
  rintro z ⟨s, ⟨hs0, hs1⟩, rfl⟩
  refine mem_lemniscate_of_normSq_le ?_
  have h1s : (0 : ℝ) ≤ 1 - s := by linarith
  simp only [goodmanPolynomial, eval_mul, eval_add, eval_X, eval_one,
    eval_sub, eval_ofNat, pow_two, Complex.real_smul, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.div_ofNat_re, Complex.div_ofNat_im]
  nlinarith [mul_nonneg (pow_nonneg hs0 0) (pow_nonneg h1s 8),
    mul_nonneg (pow_nonneg hs0 1) (pow_nonneg h1s 7),
    mul_nonneg (pow_nonneg hs0 2) (pow_nonneg h1s 6),
    mul_nonneg (pow_nonneg hs0 3) (pow_nonneg h1s 5),
    mul_nonneg (pow_nonneg hs0 4) (pow_nonneg h1s 4),
    mul_nonneg (pow_nonneg hs0 5) (pow_nonneg h1s 3),
    mul_nonneg (pow_nonneg hs0 6) (pow_nonneg h1s 2),
    mul_nonneg (pow_nonneg hs0 7) (pow_nonneg h1s 1),
    mul_nonneg (pow_nonneg hs0 8) (pow_nonneg h1s 0),
    sq_nonneg s, sq_nonneg (1 - s), hs0, h1s]

/-- Segment 2: `(1−i)/2 → 2 ⊆ {‖f‖ ≤ c}`. -/
lemma seg2_subset :
    seg ((1 - Complex.I) / 2) 2 ⊆
      lemniscate goodmanPolynomial goodmanCriticalValue := by
  simp only [seg]
  rintro z ⟨s, ⟨hs0, hs1⟩, rfl⟩
  refine mem_lemniscate_of_normSq_le ?_
  have h1s : (0 : ℝ) ≤ 1 - s := by linarith
  simp only [goodmanPolynomial, eval_mul, eval_add, eval_X, eval_one,
    eval_sub, eval_ofNat, pow_two, Complex.real_smul, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.div_ofNat_re, Complex.div_ofNat_im]
  nlinarith [mul_nonneg (pow_nonneg hs0 0) (pow_nonneg h1s 8),
    mul_nonneg (pow_nonneg hs0 1) (pow_nonneg h1s 7),
    mul_nonneg (pow_nonneg hs0 2) (pow_nonneg h1s 6),
    mul_nonneg (pow_nonneg hs0 3) (pow_nonneg h1s 5),
    mul_nonneg (pow_nonneg hs0 4) (pow_nonneg h1s 4),
    mul_nonneg (pow_nonneg hs0 5) (pow_nonneg h1s 3),
    mul_nonneg (pow_nonneg hs0 6) (pow_nonneg h1s 2),
    mul_nonneg (pow_nonneg hs0 7) (pow_nonneg h1s 1),
    mul_nonneg (pow_nonneg hs0 8) (pow_nonneg h1s 0),
    sq_nonneg s, sq_nonneg (1 - s), hs0, h1s]

/-- Segment 3: `2 → (1+i)/2 ⊆ {‖f‖ ≤ c}`. -/
lemma seg3_subset :
    seg 2 ((1 + Complex.I) / 2) ⊆
      lemniscate goodmanPolynomial goodmanCriticalValue := by
  simp only [seg]
  rintro z ⟨s, ⟨hs0, hs1⟩, rfl⟩
  refine mem_lemniscate_of_normSq_le ?_
  have h1s : (0 : ℝ) ≤ 1 - s := by linarith
  simp only [goodmanPolynomial, eval_mul, eval_add, eval_X, eval_one,
    eval_sub, eval_ofNat, pow_two, Complex.real_smul, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.div_ofNat_re, Complex.div_ofNat_im]
  nlinarith [mul_nonneg (pow_nonneg hs0 0) (pow_nonneg h1s 8),
    mul_nonneg (pow_nonneg hs0 1) (pow_nonneg h1s 7),
    mul_nonneg (pow_nonneg hs0 2) (pow_nonneg h1s 6),
    mul_nonneg (pow_nonneg hs0 3) (pow_nonneg h1s 5),
    mul_nonneg (pow_nonneg hs0 4) (pow_nonneg h1s 4),
    mul_nonneg (pow_nonneg hs0 5) (pow_nonneg h1s 3),
    mul_nonneg (pow_nonneg hs0 6) (pow_nonneg h1s 2),
    mul_nonneg (pow_nonneg hs0 7) (pow_nonneg h1s 1),
    mul_nonneg (pow_nonneg hs0 8) (pow_nonneg h1s 0),
    sq_nonneg s, sq_nonneg (1 - s), hs0, h1s]

/-- Segment 4: `(1+i)/2 → +i ⊆ {‖f‖ ≤ c}`. -/
lemma seg4_subset :
    seg ((1 + Complex.I) / 2) Complex.I ⊆
      lemniscate goodmanPolynomial goodmanCriticalValue := by
  simp only [seg]
  rintro z ⟨s, ⟨hs0, hs1⟩, rfl⟩
  refine mem_lemniscate_of_normSq_le ?_
  have h1s : (0 : ℝ) ≤ 1 - s := by linarith
  simp only [goodmanPolynomial, eval_mul, eval_add, eval_X, eval_one,
    eval_sub, eval_ofNat, pow_two, Complex.real_smul, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.div_ofNat_re, Complex.div_ofNat_im]
  nlinarith [mul_nonneg (pow_nonneg hs0 0) (pow_nonneg h1s 8),
    mul_nonneg (pow_nonneg hs0 1) (pow_nonneg h1s 7),
    mul_nonneg (pow_nonneg hs0 2) (pow_nonneg h1s 6),
    mul_nonneg (pow_nonneg hs0 3) (pow_nonneg h1s 5),
    mul_nonneg (pow_nonneg hs0 4) (pow_nonneg h1s 4),
    mul_nonneg (pow_nonneg hs0 5) (pow_nonneg h1s 3),
    mul_nonneg (pow_nonneg hs0 6) (pow_nonneg h1s 2),
    mul_nonneg (pow_nonneg hs0 7) (pow_nonneg h1s 1),
    mul_nonneg (pow_nonneg hs0 8) (pow_nonneg h1s 0),
    sq_nonneg s, sq_nonneg (1 - s), hs0, h1s]

/-- **The polyline lies inside the lemniscate** — the four segments glued. -/
lemma goodmanArc_subset_lemniscate :
    goodmanArc ⊆ lemniscate goodmanPolynomial goodmanCriticalValue := by
  unfold goodmanArc
  exact Set.union_subset
    (Set.union_subset (Set.union_subset seg1_subset seg2_subset) seg3_subset)
    seg4_subset

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
