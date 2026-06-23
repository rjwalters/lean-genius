import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue

set_option maxHeartbeats 800000

/-
# Descartes' Rule of Signs — Algebraic Proof via Polynomial Division (OQ-04)

## What This Proves

This file formalizes the **purely algebraic proof** of Descartes' Rule of Signs
following Sandy Grabiner's construction (AMM, 1999). The proof avoids Rolle's
theorem entirely, using instead:
- Polynomial arithmetic (multiplication, division, coefficient analysis)
- Induction on the number of positive roots (factoring, not differentiation)
- The Intermediate Value Theorem (for the base case: no-positive-roots implies
  even sign variations)

## The Grabiner Method

The classical proof uses Rolle's theorem: between consecutive roots of p,
the derivative p' has a root. This connects roots of p to roots of p',
enabling induction on degree via differentiation.

Grabiner's alternative: factor out positive roots one at a time via
p(x) = (x - r)·q(x) and track how sign variations change. The key
**Coefficient Transformation Lemma**: when p = (x-r)·q with r > 0,
the constant term of p is -r·q(0), which has opposite sign to q(0).
This forces at least one new sign variation, yielding V(p) ≥ V(q) + 1.

The complete algebraic proof:
1. Factor: p = (x-r₁)···(x-rₖ)·s where rᵢ > 0 are positive roots
2. Each factor (x-rᵢ) adds ≥ 1 sign variation (Grabiner's lemma)
3. s has no positive roots, so V(s) is even (via IVT sign analysis)
4. Therefore V(p) ≥ k with V(p) - k even

## Axiom Budget: 0 axioms

## References
- Grabiner, Sandy. "Descartes' Rule of Signs: Another Construction."
  American Mathematical Monthly 106(9), 854-856 (1999).

Original formalization for Lean Genius.
-/

namespace DescartesAlgebraic

open Polynomial

/-
## Part I: Coefficient Recurrence for Linear Factor Multiplication

When we multiply q(x) = bₙxⁿ + ... + b₀ by (x - r), we get
p(x) = (x - r)·q(x) with coefficients:
  coeff(p, n+1) = bₙ
  coeff(p, i) = bᵢ₋₁ - r·bᵢ     for 1 ≤ i ≤ n
  coeff(p, 0) = -r·b₀

This is the algebraic foundation of the Grabiner proof.
-/

/-- The constant term of (X - C r) * q equals -r * q.coeff 0. -/
theorem coeff_zero_X_sub_C_mul (r : ℝ) (q : ℝ[X]) :
    ((X - C r) * q).coeff 0 = -r * q.coeff 0 := by
  rw [Polynomial.coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
  simp [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]

/-- The leading coefficient of (X - C r) * q equals that of q (when q ≠ 0). -/
theorem leadingCoeff_X_sub_C_mul' (r : ℝ) (q : ℝ[X]) (hq : q ≠ 0) :
    ((X - C r) * q).leadingCoeff = q.leadingCoeff := by
  rw [Polynomial.leadingCoeff_mul (Polynomial.X_sub_C_ne_zero r) hq,
      (Polynomial.monic_X_sub_C r).leadingCoeff, one_mul]

/-- The degree of (X - C r) * q is one more than the degree of q (when q ≠ 0). -/
theorem natDegree_X_sub_C_mul' (r : ℝ) (q : ℝ[X]) (hq : q ≠ 0) :
    ((X - C r) * q).natDegree = q.natDegree + 1 := by
  rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero r) hq,
      Polynomial.natDegree_X_sub_C]

/-
## Part II: The Grabiner Multiplication Lemma
-/

/-- **Grabiner's Key Lemma**: Multiplying by a positive-root linear factor
    adds at least one sign variation to the coefficient sequence.

    This is the algebraic replacement for Rolle's theorem: where Rolle says
    "between two roots of p there's a root of p'," Grabiner says
    "factoring out a positive root increases sign variations by ≥ 1."

    From Mathlib: `Polynomial.succ_signVariations_le_X_sub_C_mul`. -/
theorem grabiner_multiplication_lemma (q : ℝ[X]) (r : ℝ) (hr : 0 < r) (hq : q ≠ 0) :
    q.signVariations + 1 ≤ ((X - C r) * q).signVariations :=
  Polynomial.succ_signVariations_le_X_sub_C_mul hr hq

/-- Factoring out a positive root increases positive root count by exactly 1. -/
theorem roots_countP_factor (r : ℝ) (q : ℝ[X]) (hr : 0 < r) (hq : q ≠ 0) :
    ((X - C r) * q).roots.countP (0 < ·) = q.roots.countP (0 < ·) + 1 := by
  have hne : (X - C r) * q ≠ 0 := mul_ne_zero (Polynomial.X_sub_C_ne_zero r) hq
  rw [Polynomial.roots_mul hne, Polynomial.roots_X_sub_C]
  simp [Multiset.countP_add, Multiset.countP_singleton, hr]

/-- Multiplying by X (root at 0) preserves sign variations. -/
theorem signVariations_X_mul_eq (p : ℝ[X]) (hp : p ≠ 0) :
    (X * p).signVariations = p.signVariations :=
  Polynomial.signVariations_X_mul hp

/-- The upper bound (from Mathlib, no Rolle's theorem). -/
theorem descartes_upper_bound (p : ℝ[X]) :
    p.roots.countP (0 < ·) ≤ p.signVariations :=
  p.roots_countP_pos_le_signVariations

/-
## Part III: Sign Variation Parity — Combinatorial Stage

signVariations is determined by the eraseLead recursive formula.
The parity depends only on whether the first and last nonzero
coefficients have the same sign.
-/

/-- The sign of a nonzero real number is nonzero as a SignType. -/
private lemma sign_ne_zero_of_ne_zero {a : ℝ} (ha : a ≠ 0) : SignType.sign a ≠ 0 := by
  rcases lt_or_gt_of_ne ha with h | h
  · simp [sign_neg h]
  · simp [sign_pos h]

/-- Constants have 0 sign variations. -/
private theorem signVariations_C_const (a : ℝ) : (C a : ℝ[X]).signVariations = 0 := by
  have : (C a : ℝ[X]) = Polynomial.monomial 0 a := by simp
  rw [this]; exact Polynomial.signVariations_monomial 0 a

/-- eraseLead preserves the degree-0 coefficient for polynomials of degree ≥ 1. -/
private lemma eraseLead_coeff_zero (p : ℝ[X]) (hd : 0 < p.natDegree) :
    p.eraseLead.coeff 0 = p.coeff 0 :=
  eraseLead_coeff_of_ne (by omega)

/-- eraseLead of a polynomial with nonzero constant term and degree ≥ 1 is nonzero. -/
private lemma eraseLead_ne_zero_of_coeff_zero_ne (p : ℝ[X]) (hc0 : p.coeff 0 ≠ 0)
    (hd : 0 < p.natDegree) : p.eraseLead ≠ 0 := by
  intro h
  have : p.eraseLead.coeff 0 = 0 := by simp [h]
  rw [eraseLead_coeff_zero p hd] at this
  exact hc0 this

/-- **Sign Variation Parity Lemma** (combinatorial):
    For p ≠ 0 with p.coeff 0 ≠ 0, the parity of signVariations is determined
    by whether the constant term and leading coefficient have the same sign.

    Proof by strong induction on support.card using the eraseLead recursive formula. -/
theorem sv_parity_from_signs (p : ℝ[X]) (hp : p ≠ 0) (hc0 : p.coeff 0 ≠ 0) :
    p.signVariations % 2 =
      if SignType.sign (p.coeff 0) = SignType.sign p.leadingCoeff then 0 else 1 := by
  suffices ∀ (n : ℕ) (q : ℝ[X]), q.support.card ≤ n → q ≠ 0 → q.coeff 0 ≠ 0 →
      q.signVariations % 2 =
        if SignType.sign (q.coeff 0) = SignType.sign q.leadingCoeff then 0 else 1 by
    exact this p.support.card p le_rfl hp hc0
  intro n
  induction n with
  | zero =>
    intro q hqn hq _
    exfalso; apply hq
    rwa [Finset.card_eq_zero, Polynomial.support_eq_empty] at hqn
  | succ n ih =>
    intro q hqn hq hqc0
    rcases Nat.eq_zero_or_pos q.natDegree with hd0 | hd_pos
    · -- Degree 0: constant polynomial, coeff 0 = leadingCoeff
      have : q.coeff 0 = q.leadingCoeff := by rw [Polynomial.leadingCoeff, hd0]
      have hsv : q.signVariations = 0 := by
        rw [eq_C_of_natDegree_eq_zero hd0]; exact signVariations_C_const q.leadingCoeff
      simp [hsv, this]
    · -- Degree ≥ 1: recursive formula via eraseLead
      have hel_ne : q.eraseLead ≠ 0 := eraseLead_ne_zero_of_coeff_zero_ne q hqc0 hd_pos
      have hel_c0 : q.eraseLead.coeff 0 ≠ 0 := by
        rwa [eraseLead_coeff_zero q hd_pos]
      have hel_card_lt : q.eraseLead.support.card < q.support.card :=
        eraseLead_support_card_lt hq
      have hih := ih q.eraseLead (by omega) hel_ne hel_c0
      rw [signVariations_eq_eraseLead_add_ite (P := q)]
      simp only [hel_ne, and_true]
      set a := SignType.sign (q.coeff 0)
      set b := SignType.sign q.eraseLead.leadingCoeff
      set c := SignType.sign q.leadingCoeff
      rw [eraseLead_coeff_zero q hd_pos] at hih
      have ha : a ≠ 0 := sign_ne_zero_of_ne_zero hqc0
      have hb : b ≠ 0 := sign_ne_zero_of_ne_zero (leadingCoeff_ne_zero.mpr hel_ne)
      have hc : c ≠ 0 := sign_ne_zero_of_ne_zero (leadingCoeff_ne_zero.mpr hq)
      cases a <;> cases b <;> cases c <;> simp_all

/-
## Part IV: No Positive Roots Implies Same-Sign Endpoints — IVT Stage

This is the one analytic ingredient (but NOT Rolle's theorem).
If a polynomial has no positive roots, then p(0) = p.coeff 0 and
p(R) for large R have the same sign. By contrapositive, if they
had opposite signs, IVT would produce a positive root.
-/

/-- Sum of lower-order terms bounded by R^(d-1) times coefficient sum. -/
private lemma lower_bound_sum (p : ℝ[X]) (R : ℝ) (hR : 1 ≤ R)
    (hd : 0 < p.natDegree) :
    |∑ i ∈ Finset.range p.natDegree, p.coeff i * R ^ i| ≤
      R ^ (p.natDegree - 1) *
        (Finset.range p.natDegree).sum (fun i => |p.coeff i|) := by
  calc |∑ i ∈ Finset.range p.natDegree, p.coeff i * R ^ i|
    ≤ ∑ i ∈ Finset.range p.natDegree, |p.coeff i * R ^ i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range p.natDegree, (|p.coeff i| * R ^ i) := by
        congr 1; ext i
        rw [abs_mul, abs_of_nonneg (pow_nonneg (le_trans zero_le_one hR) i)]
    _ ≤ ∑ i ∈ Finset.range p.natDegree, (|p.coeff i| * R ^ (p.natDegree - 1)) := by
        apply Finset.sum_le_sum; intro i hi
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply pow_le_pow_right hR
        exact Nat.lt_iff_le_pred hd |>.mp (Finset.mem_range.mp hi)
    _ = R ^ (p.natDegree - 1) *
          (Finset.range p.natDegree).sum (fun i => |p.coeff i|) := by
        rw [← Finset.sum_mul]; ring

/-- For nonzero p, there exists R > 0 where p(R) has same sign as leadingCoeff. -/
private theorem exists_eval_same_sign (p : ℝ[X]) (hp : p ≠ 0) :
    ∃ R : ℝ, 0 < R ∧ 0 < p.eval R * p.leadingCoeff := by
  rcases Nat.eq_zero_or_pos p.natDegree with hd0 | hd_pos
  · use 1, one_pos
    rw [eq_C_of_natDegree_eq_zero hd0, eval_C]
    exact mul_self_pos.mpr (leadingCoeff_ne_zero.mpr hp)
  · set d := p.natDegree
    set c := p.leadingCoeff
    have hc_ne : c ≠ 0 := leadingCoeff_ne_zero.mpr hp
    have hc_pos : 0 < |c| := abs_pos.mpr hc_ne
    set S := (Finset.range d).sum (fun i => |p.coeff i|)
    set R := max 2 (S / |c| + 2) with hR_def
    have hR_pos : (0 : ℝ) < R := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have hR_ge_1 : (1 : ℝ) ≤ R := by linarith
    have hdom : S < |c| * R := by
      calc S = |c| * (S / |c|) := by field_simp
        _ < |c| * (S / |c| + 2) := by nlinarith
        _ ≤ |c| * R := mul_le_mul_of_nonneg_left (le_max_right _ _) hc_pos.le
    have hbound := lower_bound_sum p R hR_ge_1 hd_pos
    have hR_d_split : R ^ d = R * R ^ (d - 1) := by
      rw [← pow_succ]; congr 1; omega
    have hlead : R ^ (d - 1) * S < |c| * R ^ d := by
      rw [hR_d_split]; nlinarith [pow_pos hR_pos (d - 1)]
    have heval : p.eval R = p.coeff d * R ^ d +
        ∑ i ∈ Finset.range d, p.coeff i * R ^ i := by
      rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ]; ring
    have hc_eq : p.coeff d = c := by simp [c, Polynomial.leadingCoeff]
    rw [hc_eq] at heval
    set L := ∑ i ∈ Finset.range d, p.coeff i * R ^ i
    have hL_bound : |L| < |c| * R ^ d := by
      calc |L| ≤ R ^ (d - 1) * S := hbound
        _ < |c| * R ^ d := hlead
    have hLc_bound : |L * c| < c ^ 2 * R ^ d := by
      rw [abs_mul]
      have : |L| * |c| < |c| * R ^ d * |c| := by nlinarith
      calc |L| * |c| < |c| * R ^ d * |c| := this
        _ = c ^ 2 * R ^ d := by rw [← sq_abs]; ring
    have h_csq : 0 < c ^ 2 * R ^ d := by positivity
    have h_lc_lower : -(c ^ 2 * R ^ d) < L * c := neg_lt_of_abs_lt hLc_bound
    use R, hR_pos
    rw [heval]
    have : (c * R ^ d + L) * c = c ^ 2 * R ^ d + L * c := by ring
    linarith

/-- **No positive roots implies same-sign endpoints** (IVT, not Rolle).
    If p has no positive roots and p.coeff 0 ≠ 0, then the constant term
    and leading coefficient have the same sign.

    Proof: if they had opposite signs, IVT on [0, R] (where p(R) has
    the sign of the leading coefficient) would produce a positive root. -/
theorem no_pos_roots_same_sign (p : ℝ[X]) (hp : p ≠ 0) (hc0 : p.coeff 0 ≠ 0)
    (hnr : p.roots.countP (0 < ·) = 0) :
    SignType.sign (p.coeff 0) = SignType.sign p.leadingCoeff := by
  by_contra h_ne
  obtain ⟨R, hR_pos, hR_sign⟩ := exists_eval_same_sign p hp
  have heval0 : p.eval 0 = p.coeff 0 := eval_zero p
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have h_neg : p.eval 0 * p.leadingCoeff < 0 := by
    rw [heval0]
    rcases lt_or_gt_of_ne hc0 with hc0_neg | hc0_pos <;>
    rcases lt_or_gt_of_ne hlc with hlc_neg | hlc_pos
    · exfalso; apply h_ne; simp [sign_neg hc0_neg, sign_neg hlc_neg]
    · exact mul_neg_of_neg_of_pos hc0_neg hlc_pos
    · exact mul_neg_of_pos_of_neg hc0_pos hlc_neg
    · exfalso; apply h_ne; simp [sign_pos hc0_pos, sign_pos hlc_pos]
  rcases lt_or_gt_of_ne (show p.eval 0 ≠ 0 by rwa [heval0]) with heval0_neg | heval0_pos
  · have hR_pos' : 0 < p.eval R := by nlinarith
    have hcont : ContinuousOn (fun x => p.eval x) (Set.Icc 0 R) :=
      p.continuous.continuousOn
    have h0_mem : (0 : ℝ) ∈ Set.Icc (p.eval 0) (p.eval R) := by
      constructor <;> linarith
    obtain ⟨r, ⟨hr_lo, hr_hi⟩, hr_root⟩ :=
      intermediate_value_Icc hR_pos.le hcont h0_mem
    have hr_pos : 0 < r := by
      rcases eq_or_lt_of_le hr_lo with rfl | h
      · linarith [hr_root ▸ heval0_neg]
      · exact h
    have hr_mem : r ∈ p.roots := (mem_roots hp).mpr hr_root
    have : 0 < p.roots.countP (0 < ·) :=
      Multiset.countP_pos.mpr ⟨r, hr_mem, hr_pos⟩
    omega
  · have hR_neg : p.eval R < 0 := by nlinarith
    have hcont : ContinuousOn (fun x => -(p.eval x)) (Set.Icc 0 R) :=
      p.continuous.continuousOn.neg
    have h0_mem : (0 : ℝ) ∈ Set.Icc (-(p.eval 0)) (-(p.eval R)) := by
      constructor <;> linarith
    obtain ⟨r, ⟨hr_lo, hr_hi⟩, hr_root⟩ :=
      intermediate_value_Icc hR_pos.le hcont h0_mem
    have hr_pos : 0 < r := by
      rcases eq_or_lt_of_le hr_lo with rfl | h
      · simp at hr_root; linarith
      · exact h
    have hr_is_root : p.IsRoot r := by rw [IsRoot]; linarith
    have hr_mem : r ∈ p.roots := (mem_roots hp).mpr hr_is_root
    have : 0 < p.roots.countP (0 < ·) :=
      Multiset.countP_pos.mpr ⟨r, hr_mem, hr_pos⟩
    omega

/-- No positive roots with nonzero constant term implies even sign variations. -/
theorem no_pos_roots_even_sv (p : ℝ[X]) (hp : p ≠ 0) (hc0 : p.coeff 0 ≠ 0)
    (hnr : p.roots.countP (0 < ·) = 0) :
    p.signVariations % 2 = 0 := by
  rw [sv_parity_from_signs p hp hc0, if_pos (no_pos_roots_same_sign p hp hc0 hnr)]

/-
## Part V: The Complete Algebraic Parity Proof

Combining the multiplication lemma, sign analysis, and induction
to give the full algebraic proof of Descartes' Rule.
-/

/-- For r > 0 and a ≠ 0: sign(-r * a) ≠ sign(a). -/
private lemma sign_neg_pos_mul_ne (r : ℝ) (a : ℝ) (hr : 0 < r) (ha : a ≠ 0) :
    SignType.sign (-r * a) ≠ SignType.sign a := by
  have hrn : -r < 0 := neg_lt_zero.mpr hr
  rcases lt_or_gt_of_ne ha with ha | ha
  · have hprod : 0 < -r * a := mul_pos_of_neg_of_neg hrn ha
    rw [SignType.sign_neg ha, SignType.sign_pos hprod]; decide
  · have hprod : -r * a < 0 := mul_neg_of_neg_of_pos hrn ha
    rw [SignType.sign_pos ha, SignType.sign_neg hprod]; decide

/-- **Descartes Parity — Algebraic Proof** (p.coeff 0 ≠ 0 case)

    By strong induction on natDegree, following Grabiner (1999):
    - Base (no positive roots): V(p) is even (from endpoint sign analysis)
    - Step (has positive root r): factor p = (X - C r)·s, apply IH to s -/
theorem descartes_parity_algebraic (p : ℝ[X]) (hp : p ≠ 0) (hc0 : p.coeff 0 ≠ 0) :
    ∃ k : ℕ, p.roots.countP (0 < ·) + 2 * k = p.signVariations := by
  suffices ∀ (n : ℕ) (q : ℝ[X]), q.natDegree ≤ n → q ≠ 0 → q.coeff 0 ≠ 0 →
      ∃ k : ℕ, q.roots.countP (0 < ·) + 2 * k = q.signVariations by
    exact this p.natDegree p le_rfl hp hc0
  intro n
  induction n with
  | zero =>
    intro q hqn hq hqc0
    have hqd0 : q.natDegree = 0 := Nat.eq_zero_of_le_zero hqn
    have hsv : q.signVariations = 0 := by
      rw [eq_C_of_natDegree_eq_zero hqd0]; exact signVariations_C_const q.leadingCoeff
    have hcount : q.roots.countP (0 < ·) = 0 := by
      have : q.roots.countP (0 < ·) ≤ q.signVariations := descartes_upper_bound q
      omega
    exact ⟨0, by omega⟩
  | succ n ih =>
    intro q hqn hq hqc0
    by_cases hpos : q.roots.countP (0 < ·) = 0
    · -- No positive roots: sign variations are even
      have hsv_even := no_pos_roots_even_sv q hq hqc0 hpos
      have hub := descartes_upper_bound q
      rw [hpos] at hub ⊢
      exact ⟨q.signVariations / 2, by omega⟩
    · -- Has a positive root: factor it out
      have hpos' : 0 < q.roots.countP (0 < ·) := Nat.pos_of_ne_zero hpos
      obtain ⟨r, hr_mem, hr_pos⟩ := Multiset.countP_pos.mp hpos'
      have hr_root : q.IsRoot r := (Polynomial.mem_roots hq).mp hr_mem
      obtain ⟨s, hqs⟩ := Polynomial.dvd_iff_isRoot.mpr hr_root
      have hs : s ≠ 0 := right_ne_zero_of_mul (hqs ▸ hq)
      have hdeg_q : q.natDegree = s.natDegree + 1 := by
        rw [hqs, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero r) hs,
            Polynomial.natDegree_X_sub_C]
      have hdeg : s.natDegree ≤ n := by omega
      have hsc0 : s.coeff 0 ≠ 0 := by
        intro h
        have : q.coeff 0 = -r * s.coeff 0 := by rw [hqs]; exact coeff_zero_X_sub_C_mul r s
        simp [h] at this; exact hqc0 this
      -- IH gives parity for s
      obtain ⟨j, hj⟩ := ih s hdeg hs hsc0
      -- Root count: q has one more positive root than s
      have hcount : q.roots.countP (0 < ·) = s.roots.countP (0 < ·) + 1 := by
        rw [hqs]; exact roots_countP_factor r s hr_pos hs
      -- Sign variations: q has at least one more than s
      have hsv_bound : s.signVariations + 1 ≤ q.signVariations := by
        rw [hqs]; exact grabiner_multiplication_lemma s r hr_pos hs
      -- Parity analysis via endpoint signs
      have hlc : q.leadingCoeff = s.leadingCoeff := by
        rw [hqs]; exact leadingCoeff_X_sub_C_mul' r s hs
      have hcoeff_sign : SignType.sign (q.coeff 0) ≠ SignType.sign (s.coeff 0) := by
        rw [hqs, coeff_zero_X_sub_C_mul]; exact sign_neg_pos_mul_ne r (s.coeff 0) hr_pos hsc0
      -- sv parity via endpoint sign analysis
      have hsv_q := sv_parity_from_signs q hq hqc0
      have hsv_s := sv_parity_from_signs s hs hsc0
      rw [hlc] at hsv_q
      -- Signs flip from s to q at coeff 0 but agree at leadingCoeff
      -- So the if-conditions are opposite: one 0, one 1
      have hsv_par_flip : q.signVariations % 2 = (s.signVariations % 2 + 1) % 2 := by
        rw [hsv_q, hsv_s]
        rcases SignType.sign (s.coeff 0) with _ | _ | _ <;>
        rcases SignType.sign s.leadingCoeff with _ | _ | _ <;>
        simp_all (config := { decide := true })
      -- Combine: countP and sv shifted by 1 with same parity change
      rw [hcount, Nat.add_mod, ← hj, hsv_par_flip]
      have hub := descartes_upper_bound q
      exact ⟨(q.signVariations - q.roots.countP (0 < ·)) / 2, by omega⟩

/-- **Descartes' Rule — Full Algebraic Proof** (general case)

    For any p ≠ 0: ∃ k, p.roots.countP (0 < ·) + 2*k = p.signVariations.
    When p.coeff 0 = 0, factor p = X^m · h with h.coeff 0 ≠ 0. -/
theorem descartes_full_algebraic (p : ℝ[X]) (hp : p ≠ 0) :
    ∃ k : ℕ, p.roots.countP (0 < ·) + 2 * k = p.signVariations := by
  set m := p.rootMultiplicity 0
  obtain ⟨h, hph, hndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp (0 : ℝ)
  simp only [map_zero, sub_zero] at hph
  have hh : h ≠ 0 := right_ne_zero_of_mul (hph ▸ hp)
  have hhc0 : h.coeff 0 ≠ 0 := by
    simp only [map_zero, sub_zero] at hndvd
    rwa [Polynomial.X_dvd_iff] at hndvd
  have hsv : p.signVariations = h.signVariations := by
    rw [hph]
    induction m with
    | zero => simp
    | succ m ihm =>
      rw [pow_succ, mul_assoc]
      have hxm : X ^ m * h ≠ 0 := mul_ne_zero (pow_ne_zero m Polynomial.X_ne_zero) hh
      exact (signVariations_X_mul_eq (X ^ m * h) hxm).trans ihm
  have hcount : p.roots.countP (0 < ·) = h.roots.countP (0 < ·) := by
    rw [hph]
    induction m with
    | zero => simp
    | succ m ihm =>
      rw [pow_succ, mul_assoc]
      have hxm : X ^ m * h ≠ 0 := mul_ne_zero (pow_ne_zero m Polynomial.X_ne_zero) hh
      rw [Polynomial.roots_mul (mul_ne_zero Polynomial.X_ne_zero hxm)]
      simp [Polynomial.roots_X, Multiset.countP_add, ihm]
  rw [hsv, hcount]
  exact descartes_parity_algebraic h hh hhc0

/-
## Part VI: Applications
-/

/-- If V(p) = 1, then p has exactly one positive root. -/
theorem exactly_one_root_of_one_variation (p : ℝ[X]) (hp : p ≠ 0)
    (hv : p.signVariations = 1) :
    p.roots.countP (0 < ·) = 1 := by
  have hub := descartes_upper_bound p
  obtain ⟨k, hk⟩ := descartes_full_algebraic p hp
  rw [hv] at hub hk; omega

/-- If V(p) = 0, then p has no positive roots. -/
theorem no_roots_of_zero_variations (p : ℝ[X]) (hp : p ≠ 0)
    (hv : p.signVariations = 0) :
    p.roots.countP (0 < ·) = 0 := by
  have := descartes_upper_bound p; omega

/-- The two proof methods (algebraic and analytic) give the same result. -/
theorem algebraic_agrees_with_mathlib (p : ℝ[X]) :
    p.roots.countP (0 < ·) ≤ p.signVariations :=
  descartes_upper_bound p

/-
## Summary: Algebraic vs Analytic Proof Methods

### Analytic (Rolle-based, DescartesRuleOfSigns.lean)
- **Key tool**: Rolle's theorem (between consecutive roots of p, p' has a root)
- **Induction**: On polynomial degree (differentiation reduces degree by 1)
- **Character**: Uses calculus — derivatives, continuity, mean value theorem

### Algebraic (Grabiner, this file)
- **Key tool**: Coefficient transformation ((X-r)·q has coefficients derived from q)
- **Induction**: On positive root count (factoring reduces root count by 1)
- **Character**: Uses polynomial algebra + IVT (no derivatives)
- **Advantage**: More constructive, gives algorithmic insight into sign changes

Both proofs establish the identical result: V(p) ≥ #positive_roots with even difference.
The algebraic proof is considered more elementary since it avoids calculus beyond IVT.
-/

end DescartesAlgebraic
