/-
  Erdős #1047 — OQ-02: de-axiomatizing `goodman_counterexample`
  (erdos-1047-oq-02, companion to `Erdos1047OQ02Reduction.lean`)

  ── Goal ──────────────────────────────────────────────────────────────────────

  After the parent patch the flagship `Erdos1047Problem.lean` rests on exactly ONE
  analytic assumption:

      axiom goodman_counterexample :
        ∃ z₀ ∈ lemniscate goodmanPolynomial goodmanCriticalValue,
          ¬ IsConvexComplex (componentContaining
              (lemniscate goodmanPolynomial goodmanCriticalValue) z₀)

  with  f = (X²+1)(X−2)²   and   c = 5^(3/2)/4.

  The reduction lemma `componentContaining_lemniscate_not_convex_of_chord_exits`
  (in `Erdos1047OQ02Reduction.lean`) turns this into a purely elementary task:
  exhibit one *preconnected* arc `C ⊆ {|f| ≤ c}` joining two points whose connecting
  chord pokes outside the sublevel set.

  ── The certificate (all data exact) ──────────────────────────────────────────

  Endpoints  z₀ = −i,  z₁ = +i        (the two simple roots of `z²+1`, so f = 0 there)
  Chord      t = 1/2  →  (1−t)·z₀ + t·z₁ = 0,  and  f(0) = (0+1)(0−2)² = 4 > c.
  Arc  C     the polyline through  −i → (1−i)/2 → 2 → (1+i)/2 → +i,
             threading the two non-trivial saddles (1±i)/2 of f (where |f| = c
             exactly — c = 5^(3/2)/4 is precisely the merge/onset level).

  Each of the four segments stays inside `{|f| ≤ c}` because, parametrizing
  `z(s) = (1−s)·a + s·b` and writing `x = Re z(s)`, `y = Im z(s)` (affine in s),

      |f(z(s))|² = ((x²−y²+1)² + (2xy)²)·((x−2)²+y²)²   ≤   c² = 125/16   on [0,1].

  The gap `125/16 − |f(z(s))|²` is a degree-8 polynomial in `s` with an explicit
  ALL-NONNEGATIVE degree-8 Bernstein decomposition, so each bound is closed by
  `nlinarith` fed the nine boundary atoms `sᵏ(1−s)^(8−k) ≥ 0` (k = 0…8): the gap is
  exactly a nonnegative linear combination of these.  (Bernstein coefficients
  verified by `research/problems/erdos-1047-oq-02/chord_exits_sos_certificate.py`.)

  No new axioms are introduced.  `goodman_counterexample_proof` discharges the
  parent axiom outright; `grunsky_false_of_chord_exit` re-derives the headline
  `¬ grunskyConjecture` from it without any axiom.

  STATUS: build-pending (transcription of a fully-verified analytic certificate).
-/

import Proofs.Erdos1047Problem
import Proofs.Erdos1047OQ02Reduction
import Mathlib.Tactic

open Polynomial Set
open Erdos1047

namespace Erdos1047OQ02ChordExit

/-- `f = (X²+1)(X−2)²` evaluated, in a `ring`-friendly form.  We write the constant
    `2` as `1 + 1` so that the downstream `re`/`im` expansion needs only the very
    stable `Complex.one_re`/`one_im`/`add_re`/`add_im` simp lemmas. -/
lemma goodman_eval (w : ℂ) :
    goodmanPolynomial.eval w = (w * w + 1) * ((w - (1 + 1)) * (w - (1 + 1))) := by
  simp only [goodmanPolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_ofNat]
  ring

/-- `|f(w)|²` as a real polynomial in `Re w`, `Im w`. -/
lemma normSq_goodman_eval (w : ℂ) :
    Complex.normSq (goodmanPolynomial.eval w)
      = ((w.re ^ 2 - w.im ^ 2 + 1) ^ 2 + (2 * w.re * w.im) ^ 2)
          * ((w.re - 2) ^ 2 + w.im ^ 2) ^ 2 := by
  rw [goodman_eval]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  ring

/-- `c = 5^(3/2)/4 ≥ 0`. -/
lemma goodmanCriticalValue_nonneg : 0 ≤ goodmanCriticalValue := by
  unfold goodmanCriticalValue; positivity

/-- `c² = 125/16` (so `c` is the saddle level: `|f((1±i)/2)|² = 125/16`). -/
lemma goodmanCriticalValue_sq : goodmanCriticalValue ^ 2 = 125 / 16 := by
  have h5 : (0:ℝ) ≤ 5 := by norm_num
  have e1 : ((5:ℝ) ^ (3 / 2 : ℝ)) ^ 2 = (5:ℝ) ^ ((3 / 2 : ℝ) * 2) := by
    rw [← Real.rpow_natCast ((5:ℝ) ^ (3 / 2 : ℝ)) 2, ← Real.rpow_mul h5]
    norm_num
  have e2 : (5:ℝ) ^ ((3 / 2 : ℝ) * 2) = 125 := by
    rw [show (3 / 2 : ℝ) * 2 = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  unfold goodmanCriticalValue
  rw [div_pow, e1, e2]
  norm_num

/-- Squaring criterion: a nonnegative `c` with `|z|² ≤ c²` bounds `‖z‖ ≤ c`. -/
lemma norm_le_of_normSq_le {z : ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : Complex.normSq z ≤ c ^ 2) : ‖z‖ ≤ c := by
  have hz : ‖z‖ ^ 2 = Complex.normSq z := Complex.sq_norm z
  nlinarith [norm_nonneg z, hz, h, hc]

/-! ### The four arc endpoints (as exact `⟨re, im⟩` complex numbers). -/

/-- `−i` -/
noncomputable def zA : ℂ := ⟨0, -1⟩
/-- `(1−i)/2` -/
noncomputable def zB : ℂ := ⟨1 / 2, -1 / 2⟩
/-- `2` -/
noncomputable def zC : ℂ := ⟨2, 0⟩
/-- `(1+i)/2` -/
noncomputable def zD : ℂ := ⟨1 / 2, 1 / 2⟩
/-- `+i` -/
noncomputable def zE : ℂ := ⟨0, 1⟩

@[simp] lemma zA_re : zA.re = 0 := rfl
@[simp] lemma zA_im : zA.im = -1 := rfl
@[simp] lemma zB_re : zB.re = 1 / 2 := rfl
@[simp] lemma zB_im : zB.im = -1 / 2 := rfl
@[simp] lemma zC_re : zC.re = 2 := rfl
@[simp] lemma zC_im : zC.im = 0 := rfl
@[simp] lemma zD_re : zD.re = 1 / 2 := rfl
@[simp] lemma zD_im : zD.im = 1 / 2 := rfl
@[simp] lemma zE_re : zE.re = 0 := rfl
@[simp] lemma zE_im : zE.im = 1 := rfl

/-- The polyline arc `C = [zA,zB] ∪ [zB,zC] ∪ [zC,zD] ∪ [zD,zE]`. -/
def arc : Set ℂ :=
  segment ℝ zA zB ∪ segment ℝ zB zC ∪ segment ℝ zC zD ∪ segment ℝ zD zE

/-- The arc is preconnected: consecutive segments share an endpoint. -/
lemma arc_isPreconnected : IsPreconnected arc := by
  have h1 : IsPreconnected (segment ℝ zA zB) := (convex_segment _ _).isPreconnected
  have h2 : IsPreconnected (segment ℝ zB zC) := (convex_segment _ _).isPreconnected
  have h3 : IsPreconnected (segment ℝ zC zD) := (convex_segment _ _).isPreconnected
  have h4 : IsPreconnected (segment ℝ zD zE) := (convex_segment _ _).isPreconnected
  have h12 : IsPreconnected (segment ℝ zA zB ∪ segment ℝ zB zC) :=
    h1.union zB (right_mem_segment ℝ zA zB) (left_mem_segment ℝ zB zC) h2
  have h123 : IsPreconnected (segment ℝ zA zB ∪ segment ℝ zB zC ∪ segment ℝ zC zD) :=
    h12.union zC (Or.inr (right_mem_segment ℝ zB zC)) (left_mem_segment ℝ zC zD) h3
  exact h123.union zD
    (Or.inr (right_mem_segment ℝ zC zD)) (left_mem_segment ℝ zD zE) h4

/-! ### Each segment lies inside the Goodman sublevel set. -/

/-- Reduce `segment ℝ a b ⊆ {|f| ≤ c}` to a degree-8 polynomial bound in the
    segment parameter `s`. -/
lemma segment_subset_lemniscate
    {a b : ℂ} (hbound : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        Complex.normSq (goodmanPolynomial.eval ((1 - s) • a + s • b)) ≤ 125 / 16) :
    segment ℝ a b ⊆ lemniscate goodmanPolynomial goodmanCriticalValue := by
  rw [segment_eq_image ℝ a b]
  rintro w ⟨s, ⟨hs0, hs1⟩, rfl⟩
  show ‖goodmanPolynomial.eval ((1 - s) • a + s • b)‖ ≤ goodmanCriticalValue
  refine norm_le_of_normSq_le goodmanCriticalValue_nonneg ?_
  rw [goodmanCriticalValue_sq]
  exact hbound s hs0 hs1

lemma seg_AB_subset :
    segment ℝ zA zB ⊆ lemniscate goodmanPolynomial goodmanCriticalValue := by
  apply segment_subset_lemniscate
  intro s hs0 hs1
  have h1s : (0:ℝ) ≤ 1 - s := by linarith
  have hre : ((1 - s) • zA + s • zB).re = s / 2 := by
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zA_re, zA_im, zB_re, zB_im]; ring
  have him : ((1 - s) • zA + s • zB).im = s / 2 - 1 := by
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zA_re, zA_im, zB_re, zB_im]; ring
  rw [normSq_goodman_eval, hre, him]
  nlinarith [mul_nonneg (pow_nonneg hs0 0) (pow_nonneg h1s 8),
    mul_nonneg (pow_nonneg hs0 1) (pow_nonneg h1s 7),
    mul_nonneg (pow_nonneg hs0 2) (pow_nonneg h1s 6),
    mul_nonneg (pow_nonneg hs0 3) (pow_nonneg h1s 5),
    mul_nonneg (pow_nonneg hs0 4) (pow_nonneg h1s 4),
    mul_nonneg (pow_nonneg hs0 5) (pow_nonneg h1s 3),
    mul_nonneg (pow_nonneg hs0 6) (pow_nonneg h1s 2),
    mul_nonneg (pow_nonneg hs0 7) (pow_nonneg h1s 1),
    mul_nonneg (pow_nonneg hs0 8) (pow_nonneg h1s 0)]

lemma seg_BC_subset :
    segment ℝ zB zC ⊆ lemniscate goodmanPolynomial goodmanCriticalValue := by
  apply segment_subset_lemniscate
  intro s hs0 hs1
  have h1s : (0:ℝ) ≤ 1 - s := by linarith
  have hre : ((1 - s) • zB + s • zC).re = 3 * s / 2 + 1 / 2 := by
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zB_re, zB_im, zC_re, zC_im]; ring
  have him : ((1 - s) • zB + s • zC).im = s / 2 - 1 / 2 := by
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zB_re, zB_im, zC_re, zC_im]; ring
  rw [normSq_goodman_eval, hre, him]
  nlinarith [mul_nonneg (pow_nonneg hs0 0) (pow_nonneg h1s 8),
    mul_nonneg (pow_nonneg hs0 1) (pow_nonneg h1s 7),
    mul_nonneg (pow_nonneg hs0 2) (pow_nonneg h1s 6),
    mul_nonneg (pow_nonneg hs0 3) (pow_nonneg h1s 5),
    mul_nonneg (pow_nonneg hs0 4) (pow_nonneg h1s 4),
    mul_nonneg (pow_nonneg hs0 5) (pow_nonneg h1s 3),
    mul_nonneg (pow_nonneg hs0 6) (pow_nonneg h1s 2),
    mul_nonneg (pow_nonneg hs0 7) (pow_nonneg h1s 1),
    mul_nonneg (pow_nonneg hs0 8) (pow_nonneg h1s 0)]

lemma seg_CD_subset :
    segment ℝ zC zD ⊆ lemniscate goodmanPolynomial goodmanCriticalValue := by
  apply segment_subset_lemniscate
  intro s hs0 hs1
  have h1s : (0:ℝ) ≤ 1 - s := by linarith
  have hre : ((1 - s) • zC + s • zD).re = 2 - 3 * s / 2 := by
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zC_re, zC_im, zD_re, zD_im]; ring
  have him : ((1 - s) • zC + s • zD).im = s / 2 := by
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zC_re, zC_im, zD_re, zD_im]; ring
  rw [normSq_goodman_eval, hre, him]
  nlinarith [mul_nonneg (pow_nonneg hs0 0) (pow_nonneg h1s 8),
    mul_nonneg (pow_nonneg hs0 1) (pow_nonneg h1s 7),
    mul_nonneg (pow_nonneg hs0 2) (pow_nonneg h1s 6),
    mul_nonneg (pow_nonneg hs0 3) (pow_nonneg h1s 5),
    mul_nonneg (pow_nonneg hs0 4) (pow_nonneg h1s 4),
    mul_nonneg (pow_nonneg hs0 5) (pow_nonneg h1s 3),
    mul_nonneg (pow_nonneg hs0 6) (pow_nonneg h1s 2),
    mul_nonneg (pow_nonneg hs0 7) (pow_nonneg h1s 1),
    mul_nonneg (pow_nonneg hs0 8) (pow_nonneg h1s 0)]

lemma seg_DE_subset :
    segment ℝ zD zE ⊆ lemniscate goodmanPolynomial goodmanCriticalValue := by
  apply segment_subset_lemniscate
  intro s hs0 hs1
  have h1s : (0:ℝ) ≤ 1 - s := by linarith
  have hre : ((1 - s) • zD + s • zE).re = 1 / 2 - s / 2 := by
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zD_re, zD_im, zE_re, zE_im]; ring
  have him : ((1 - s) • zD + s • zE).im = s / 2 + 1 / 2 := by
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zD_re, zD_im, zE_re, zE_im]; ring
  rw [normSq_goodman_eval, hre, him]
  nlinarith [mul_nonneg (pow_nonneg hs0 0) (pow_nonneg h1s 8),
    mul_nonneg (pow_nonneg hs0 1) (pow_nonneg h1s 7),
    mul_nonneg (pow_nonneg hs0 2) (pow_nonneg h1s 6),
    mul_nonneg (pow_nonneg hs0 3) (pow_nonneg h1s 5),
    mul_nonneg (pow_nonneg hs0 4) (pow_nonneg h1s 4),
    mul_nonneg (pow_nonneg hs0 5) (pow_nonneg h1s 3),
    mul_nonneg (pow_nonneg hs0 6) (pow_nonneg h1s 2),
    mul_nonneg (pow_nonneg hs0 7) (pow_nonneg h1s 1),
    mul_nonneg (pow_nonneg hs0 8) (pow_nonneg h1s 0)]

/-- The whole arc lies inside the Goodman sublevel set. -/
lemma arc_subset_lemniscate :
    arc ⊆ lemniscate goodmanPolynomial goodmanCriticalValue := by
  unfold arc
  exact union_subset (union_subset (union_subset seg_AB_subset seg_BC_subset)
    seg_CD_subset) seg_DE_subset

/-- The chord midpoint of `zA = −i`, `zE = +i` (at `t = 1/2`) is the origin. -/
lemma chord_midpoint : (1 - (1 / 2 : ℝ)) • zA + (1 / 2 : ℝ) • zE = 0 := by
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re,
      Complex.zero_im, zA_re, zA_im, zE_re, zE_im] <;> ring

/-- The connecting chord pokes outside: `|f(0)| = 4 > c`. -/
lemma chord_exits :
    goodmanCriticalValue
      < ‖goodmanPolynomial.eval ((1 - (1 / 2 : ℝ)) • zA + (1 / 2 : ℝ) • zE)‖ := by
  rw [chord_midpoint, goodman_eval]
  have hval : (((0:ℂ) * 0 + 1) * ((0 - (1 + 1)) * (0 - (1 + 1)))) = (4 : ℂ) := by ring
  rw [hval]
  have h4 : ‖(4 : ℂ)‖ = 4 := by simp
  rw [h4]
  nlinarith [goodmanCriticalValue_nonneg, goodmanCriticalValue_sq]

/-- **De-axiomatization of `goodman_counterexample`.**  The `−i`-component of the
    Goodman lemniscate `{|f| ≤ 5^(3/2)/4}` is not convex — proved from the explicit
    chord-exit certificate via the registered topological reduction. -/
theorem goodman_counterexample_proof :
    ∃ z₀ ∈ lemniscate goodmanPolynomial goodmanCriticalValue,
      ¬ IsConvexComplex (componentContaining
        (lemniscate goodmanPolynomial goodmanCriticalValue) z₀) := by
  refine ⟨zA, ?_, ?_⟩
  · exact arc_subset_lemniscate (Or.inl (Or.inl (Or.inl (left_mem_segment ℝ zA zB))))
  · refine Erdos1047OQ02.componentContaining_lemniscate_not_convex_of_chord_exits
      arc_isPreconnected arc_subset_lemniscate
      (Or.inl (Or.inl (Or.inl (left_mem_segment ℝ zA zB))))
      (Or.inr (right_mem_segment ℝ zD zE))
      (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) chord_exits

/-- The faithful Grunsky statement is false, with NO axiom: re-derived from the
    de-axiomatized counterexample. -/
theorem grunsky_false_of_chord_exit : ¬ grunskyConjecture := by
  intro h
  obtain ⟨z₀, hz₀, hnc⟩ := goodman_counterexample_proof
  exact hnc (h goodmanPolynomial goodmanPolynomial_monic goodmanPolynomial_degree_pos
    goodmanCriticalValue (by unfold goodmanCriticalValue; positivity) z₀ hz₀)

end Erdos1047OQ02ChordExit
