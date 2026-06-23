/-
  Hölder's Inequality Equality Case
  Open Question: cauchy-schwarz-oq-03-oq-01

  Formalizes when equality holds in Hölder's (and Cauchy-Schwarz) inequality:

  Cauchy-Schwarz case (p = q = 2):
    (∑ f_i · g_i)² = (∑ f_i²)(∑ g_i²) iff f and g are proportional.
    Proved via Lagrange's identity: the double sum of squared cross-terms
    ∑_i ∑_j (f_i·g_j - f_j·g_i)² = 0 iff all cross-terms vanish.

  Inner product space case:
    |inner u v| = ‖u‖·‖v‖ iff ∃ c, u = c·v (Mathlib's norm_inner_eq_norm_iff).

  References:
  - Lagrange (1773): identity for 2×2 determinants
  - Hardy-Littlewood-Pólya "Inequalities" (1934) Ch. 2, Theorem 15
-/

import Mathlib

open Finset NNReal Real

namespace CauchySchwarzOQ03OQ01

-- ============================================================================
-- Part I: Finite Sum Equality via Lagrange Identity
-- ============================================================================

/-
From CauchySchwarzOQ03.lean, we have the Lagrange identity:
  ∑_i ∑_j (f_i·g_j - f_j·g_i)² = 2·[(∑f²)(∑g²) - (∑fg)²]

Equality in CS means (∑fg)² = (∑f²)(∑g²), so the Lagrange RHS = 0.
A sum of non-negative terms equals zero iff each term is zero.
So equality holds iff f_i·g_j = f_j·g_i for all i, j ∈ s.
-/

/-- Lagrange identity: the double sum of squared cross-terms equals
    twice the Cauchy-Schwarz deficit. -/
theorem lagrange_identity {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    ∑ i ∈ s, ∑ j ∈ s, (f i * g j - f j * g i) ^ 2 =
      2 * ((∑ i ∈ s, f i ^ 2) * (∑ i ∈ s, g i ^ 2) -
           (∑ i ∈ s, f i * g i) ^ 2) := by
  simp_rw [sub_sq, sum_add_distrib, Finset.sum_sub_distrib]
  have ha : ∑ i ∈ s, ∑ j ∈ s, (f i * g j) ^ 2 =
      (∑ i ∈ s, f i ^ 2) * (∑ j ∈ s, g j ^ 2) := by
    simp_rw [mul_pow, ← mul_sum, ← sum_mul]
  have hc : ∑ i ∈ s, ∑ j ∈ s, (f j * g i) ^ 2 =
      (∑ j ∈ s, f j ^ 2) * (∑ i ∈ s, g i ^ 2) := by
    rw [sum_comm]
    simp_rw [mul_pow, ← mul_sum, ← sum_mul]
  have hb : ∑ i ∈ s, ∑ j ∈ s, 2 * (f i * g j) * (f j * g i) =
      2 * (∑ i ∈ s, f i * g i) ^ 2 := by
    simp_rw [sq, sum_mul, mul_sum]
    congr 1; ext i; congr 1; ext j; ring
  rw [ha, hc, hb]; ring

/-- A sum of squares over a Finset is zero iff each term is zero. -/
theorem sum_sq_eq_zero_iff {ι : Type*} (s : Finset ι) (h : ι → ℝ) :
    ∑ i ∈ s, h i ^ 2 = 0 ↔ ∀ i ∈ s, h i = 0 := by
  constructor
  · intro hsum i hi
    have hnn : ∀ j ∈ s, 0 ≤ h j ^ 2 := fun j _ => sq_nonneg _
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum i hi
    exact (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp this
  · intro hall
    exact Finset.sum_eq_zero fun i hi => by rw [hall i hi, sq, mul_zero]

/-- Double sum of squares is zero iff each term is zero. -/
theorem double_sum_sq_eq_zero_iff {ι : Type*} (s : Finset ι) (h : ι → ι → ℝ) :
    ∑ i ∈ s, ∑ j ∈ s, h i j ^ 2 = 0 ↔ ∀ i ∈ s, ∀ j ∈ s, h i j = 0 := by
  constructor
  · intro hsum i hi j hj
    have hnn_outer : ∀ k ∈ s, 0 ≤ ∑ l ∈ s, h k l ^ 2 :=
      fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg _
    have h_inner_zero := (Finset.sum_eq_zero_iff_of_nonneg hnn_outer).mp hsum i hi
    exact (sum_sq_eq_zero_iff s (h i)).mp h_inner_zero j hj
  · intro hall
    exact Finset.sum_eq_zero fun i hi =>
      Finset.sum_eq_zero fun j hj => by rw [hall i hi j hj, sq, mul_zero]

/-- **Cauchy-Schwarz Equality Characterization (Finite Sums)**:
    Equality holds iff all cross-terms f_i·g_j - f_j·g_i vanish,
    which means f and g are "proportional" in the sense that
    f_i·g_j = f_j·g_i for all i, j. -/
theorem cauchy_schwarz_eq_iff {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    (∑ i ∈ s, f i * g i) ^ 2 = (∑ i ∈ s, f i ^ 2) * (∑ i ∈ s, g i ^ 2) ↔
    ∀ i ∈ s, ∀ j ∈ s, f i * g j = f j * g i := by
  have h_lagrange := lagrange_identity s f g
  constructor
  · intro heq
    have h_zero : ∑ i ∈ s, ∑ j ∈ s, (f i * g j - f j * g i) ^ 2 = 0 := by
      linarith
    have h_all := (double_sum_sq_eq_zero_iff s (fun i j => f i * g j - f j * g i)).mp h_zero
    intro i hi j hj
    exact sub_eq_zero.mp (h_all i hi j hj)
  · intro hprop
    have h_zero : ∑ i ∈ s, ∑ j ∈ s, (f i * g j - f j * g i) ^ 2 = 0 :=
      (double_sum_sq_eq_zero_iff s _).mpr fun i hi j hj =>
        sub_eq_zero.mpr (hprop i hi j hj)
    linarith

-- ============================================================================
-- Part II: Proportionality from Cross-Term Condition
-- ============================================================================

/-
The condition ∀ i j, f_i·g_j = f_j·g_i means the 2×2 determinants vanish.
If some g_k ≠ 0, then f_i = (f_k/g_k)·g_i for all i.
-/

/-- If all cross-terms vanish and some g_k ≠ 0, then f = c · g
    where c = f_k / g_k. -/
theorem proportional_of_cross_terms_zero {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, f i * g j = f j * g i)
    {k : ι} (hk : k ∈ s) (hgk : g k ≠ 0) :
    ∀ i ∈ s, f i = (f k / g k) * g i := by
  intro i hi
  have h := hcross i hi k hk
  field_simp at h ⊢
  linarith

/-- **Proportionality implies Cauchy-Schwarz equality** (reverse direction):
    If f = c · g on s, then (∑fᵢgᵢ)² = (∑fᵢ²)(∑gᵢ²). -/
theorem cauchy_schwarz_eq_of_proportional {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (c : ℝ) (hprop : ∀ i ∈ s, f i = c * g i) :
    (∑ i ∈ s, f i * g i) ^ 2 = (∑ i ∈ s, f i ^ 2) * (∑ i ∈ s, g i ^ 2) := by
  have h1 : ∀ i ∈ s, f i * g i = c * g i ^ 2 :=
    fun i hi => by rw [hprop i hi]; ring
  have h2 : ∀ i ∈ s, f i ^ 2 = c ^ 2 * g i ^ 2 :=
    fun i hi => by rw [hprop i hi]; ring
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- **Full Cauchy-Schwarz Equality Characterization with Proportionality**:
    When g is not identically zero on s, equality holds iff f is a
    scalar multiple of g (proportional). -/
theorem cauchy_schwarz_eq_iff_proportional {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    {k : ι} (hk : k ∈ s) (hgk : g k ≠ 0) :
    (∑ i ∈ s, f i * g i) ^ 2 = (∑ i ∈ s, f i ^ 2) * (∑ i ∈ s, g i ^ 2) ↔
    ∃ c : ℝ, ∀ i ∈ s, f i = c * g i := by
  constructor
  · intro heq
    have hcross := cauchy_schwarz_eq_iff s f g |>.mp heq
    exact ⟨f k / g k, proportional_of_cross_terms_zero s f g hcross hk hgk⟩
  · rintro ⟨c, hprop⟩
    exact cauchy_schwarz_eq_of_proportional s f g c hprop

-- ============================================================================
-- Part III: Inner Product Space Equality Case
-- ============================================================================

/-- **Cauchy-Schwarz equality for inner product spaces**:
    ‖inner u v‖ = ‖u‖·‖v‖ iff u and v are scalar multiples.
    This is the abstract version of the finite-sum equality case.
    (Uses Mathlib's norm_inner_eq_norm_iff.) -/
theorem cauchy_schwarz_eq_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u v : E) (hu : u ≠ 0) (hv : v ≠ 0) :
    ‖@inner ℝ _ _ u v‖ = ‖u‖ * ‖v‖ ↔ ∃ c : ℝ, u = c • v := by
  constructor
  · intro h
    obtain ⟨r, hr_ne, hr⟩ := (norm_inner_eq_norm_iff hu hv).mp h
    exact ⟨r⁻¹, by rw [hr, smul_smul, inv_mul_cancel₀ hr_ne, one_smul]⟩
  · intro ⟨c, hc⟩
    rw [hc, inner_smul_left, real_inner_self_eq_norm_sq, norm_smul]
    simp only [starRingEnd_apply, star_trivial, Real.norm_eq_abs]
    rw [abs_mul, abs_of_nonneg (sq_nonneg ‖v‖)]
    ring

/-- Corollary: absolute value form of the equality condition. -/
theorem cauchy_schwarz_abs_eq_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u v : E) (hu : u ≠ 0) (hv : v ≠ 0) :
    |@inner ℝ _ _ u v| = ‖u‖ * ‖v‖ ↔ ∃ c : ℝ, u = c • v := by
  rw [← Real.norm_eq_abs]
  exact cauchy_schwarz_eq_inner u v hu hv

-- ============================================================================
-- Part IV: General Hölder Equality (Description)
-- ============================================================================

/-
## Summary of Equality Characterizations

### Cauchy-Schwarz (p = q = 2):
  (∑ f_i·g_i)² = (∑ f_i²)(∑ g_i²)
  ⟺ ∀ i,j ∈ s, f_i·g_j = f_j·g_i          (cross-term condition)
  ⟺ ∃ c, ∀ i ∈ s, f_i = c·g_i              (proportionality, when some g_i ≠ 0)

### Inner Product Space:
  ‖inner u v‖ = ‖u‖·‖v‖
  ⟺ ∃ c : ℝ, u = c • v                      (Mathlib's norm_inner_eq_norm_iff)

### General Hölder (p, q conjugate):
  ∑ f_i·g_i = ‖f‖_p · ‖g‖_q
  ⟺ ∃ λ ≥ 0, ∀ i, f_i^p = λ · g_i^q        (power proportionality)
  This follows from Young's equality: ab = a^p/p + b^q/q ⟺ a^p = b^q.
  The full formal proof of the general Hölder equality case requires
  showing that equality in ∑-Young implies pointwise equality,
  using the strict concavity of the logarithm.

### Equality in Integral Form:
  ∫ f·g dμ = ‖f‖_p · ‖g‖_q
  ⟺ ∃ λ ≥ 0, f^p = λ · g^q a.e.            (a.e. power proportionality)
-/

/-- Hölder's inequality (NNReal finite sums, from Mathlib). -/
theorem holder_nnreal {ι : Type*} (s : Finset ι) (f g : ι → ℝ≥0)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    ∑ i ∈ s, f i * g i ≤
      (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) :=
  NNReal.inner_le_Lp_mul_Lq s f g hpq

/-- Cauchy-Schwarz for finite sums (consequence of Lagrange identity). -/
theorem cauchy_schwarz_finite {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * (∑ i ∈ s, g i ^ 2) := by
  have h_nn : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, (f i * g j - f j * g i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith [lagrange_identity s f g]

/-- Concrete example: equality when vectors are proportional.
    f = (1, 2, 3), g = (2, 4, 6) = 2·f, so equality holds. -/
example : (1*2 + 2*4 + 3*6 : ℝ)^2 = (1^2 + 2^2 + 3^2) * (2^2 + 4^2 + 6^2) := by
  norm_num

/-- Concrete example: strict inequality when not proportional.
    f = (1, 0), g = (0, 1), inner product = 0 < 1 = ‖f‖·‖g‖. -/
example : (1*0 + 0*1 : ℝ)^2 < (1^2 + 0^2) * (0^2 + 1^2) := by
  norm_num

-- ============================================================================
-- Part V: General Hölder Equality — Conjugate Exponent Identities
-- ============================================================================

/-
For conjugate exponents p, q with 1 < p and 1/p + 1/q = 1:
  - q = p/(p-1)
  - (p-1)(q-1) = 1
  - q/p + 1 = q (key for the power proportionality proof)
  - p + q = pq
These identities are used throughout the Hölder equality analysis.
-/

/-- For Hölder conjugates, q = p/(p-1). -/
theorem conj_eq_div {p q : ℝ} (hp : 1 < p) (hinv : 1 / p + 1 / q = 1) :
    q = p / (p - 1) := by
  have hp_pos : (0 : ℝ) < p := lt_trans one_pos hp
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hq_pos : (0 : ℝ) < q := by
    by_contra h
    push_neg at h
    have hq_le : q ≤ 0 := h
    have : 1 / q ≤ 0 := div_nonpos_iff.mpr (Or.inl ⟨le_of_lt one_pos, hq_le⟩)
    have : 1 / p < 1 := by rw [div_lt_one hp_pos]; exact hp
    linarith
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  field_simp at hinv ⊢; nlinarith

/-- For Hölder conjugates, (p-1)(q-1) = 1. -/
theorem conj_sub_one_mul {p q : ℝ} (hp : 1 < p) (hinv : 1 / p + 1 / q = 1) :
    (p - 1) * (q - 1) = 1 := by
  have hp_ne : p ≠ 0 := ne_of_gt (lt_trans one_pos hp)
  have hq_ne : q ≠ 0 := by
    intro heq; rw [heq, div_zero, add_zero] at hinv
    have : 1 / p < 1 := by rw [div_lt_one (by linarith : (0:ℝ) < p)]; exact hp
    linarith
  have := hinv
  field_simp at this
  nlinarith

/-- For Hölder conjugates, q/p + 1 = q. -/
theorem conj_q_div_p_add_one {p q : ℝ} (hp : 1 < p) (hinv : 1 / p + 1 / q = 1) :
    q / p + 1 = q := by
  have hp_ne : p ≠ 0 := ne_of_gt (lt_trans one_pos hp)
  field_simp; linarith [conj_sub_one_mul hp hinv]

/-- For Hölder conjugates, 1 < q. -/
theorem conj_one_lt_q {p q : ℝ} (hp : 1 < p) (hinv : 1 / p + 1 / q = 1) :
    1 < q := by
  have hq := conj_eq_div hp hinv
  rw [hq]
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  rw [one_lt_div hp1]
  linarith

/-- For Hölder conjugates, p + q = p * q. -/
theorem conj_add_eq_mul {p q : ℝ} (hp : 1 < p) (hinv : 1 / p + 1 / q = 1) :
    p + q = p * q := by
  have hp_ne : p ≠ 0 := ne_of_gt (lt_trans one_pos hp)
  have hq_ne : q ≠ 0 := ne_of_gt (lt_trans one_pos (conj_one_lt_q hp hinv))
  field_simp at hinv; linarith

-- ============================================================================
-- Part VI: Young's Equality Case
-- ============================================================================

/-
Young's inequality: a·b ≤ a^p/p + b^q/q for a, b ≥ 0, p, q conjugate.

Equality holds iff a^p = b^q (power proportionality).

Forward direction (a^p = b^q → equality): algebraic.
  If a^p = b^q = c, then RHS = c/p + c/q = c·(1/p + 1/q) = c.
  LHS = a·b = c^{1/p}·c^{1/q} = c^{1/p+1/q} = c.

Reverse direction (equality → a^p = b^q): uses strict convexity.
  The function h(t) = t^p/p - t + 1/q is strictly convex for p > 1,
  has unique minimum at t = 1 with h(1) = 0. So h(t) ≥ 0 with
  equality iff t = 1. Setting t = a·b^{1-q} gives a^p = b^q.
-/

/-- Young's inequality deficit: the quantity a^p/p + b^q/q - a·b ≥ 0.
    A sum of these deficits being zero implies each deficit is zero. -/
noncomputable def youngDeficit (p q a b : ℝ) : ℝ := a ^ p / p + b ^ q / q - a * b

/-- The Young deficit is non-negative (restates Young's inequality).
    Follows from convexity of exp: a·b = exp(log a + log b) ≤ a^p/p + b^q/q. -/
theorem youngDeficit_nonneg {p q : ℝ} (hp : 1 < p) (hinv : 1 / p + 1 / q = 1)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ youngDeficit p q a b := by
  unfold youngDeficit
  have hp_pos : (0 : ℝ) < p := by linarith
  have hq : 1 < q := conj_one_lt_q hp hinv
  have hq_pos : (0 : ℝ) < q := by linarith
  by_cases ha0 : a = 0
  · rw [ha0, Real.zero_rpow hp_pos.ne', zero_div, zero_add, zero_mul, sub_zero]
    exact div_nonneg (Real.rpow_nonneg hb q) hq_pos.le
  by_cases hb0 : b = 0
  · rw [hb0, Real.zero_rpow hq_pos.ne', zero_div, add_zero, mul_zero, sub_zero]
    exact div_nonneg (Real.rpow_nonneg ha p) hp_pos.le
  -- Both a, b > 0: use convexity of exp
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  set x := Real.log a * p with hx_def
  set y := Real.log b * q with hy_def
  have hconv := convexOn_exp.2 (Set.mem_univ x) (Set.mem_univ y)
    (show (0 : ℝ) ≤ 1/p by positivity) (show (0 : ℝ) ≤ 1/q by positivity) hinv
  simp only [smul_eq_mul] at hconv
  have hmix : 1/p * x + 1/q * y = Real.log a + Real.log b := by
    simp only [hx_def, hy_def]; field_simp
  rw [hmix, Real.exp_add, Real.exp_log ha_pos, Real.exp_log hb_pos] at hconv
  have hex : Real.exp x = a ^ p := by
    rw [hx_def]; exact (Real.rpow_def_of_pos ha_pos p).symm
  have hey : Real.exp y = b ^ q := by
    rw [hy_def]; exact (Real.rpow_def_of_pos hb_pos q).symm
  rw [hex, hey] at hconv
  -- hconv: a * b ≤ 1/p * a^p + 1/q * b^q
  -- Goal: 0 ≤ a^p/p + b^q/q - a*b
  have h1 : 1 / p * a ^ p = a ^ p / p := by ring
  have h2 : 1 / q * b ^ q = b ^ q / q := by ring
  linarith

/-- Forward direction of Young equality: a^p = b^q → deficit = 0. -/
private theorem youngDeficit_eq_zero_of_eq {p q : ℝ} (hp : 1 < p)
    (hinv : 1 / p + 1 / q = 1) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (heq : a ^ p = b ^ q) : youngDeficit p q a b = 0 := by
  unfold youngDeficit
  have hp_pos : (0 : ℝ) < p := by linarith
  have hq_pos : (0 : ℝ) < q := lt_trans one_pos (conj_one_lt_q hp hinv)
  by_cases ha0 : a = 0
  · have hap : a ^ p = 0 := by rw [ha0]; exact Real.zero_rpow hp_pos.ne'
    have hbq : b ^ q = 0 := heq ▸ hap
    have hb0 : b = 0 := by
      by_contra hb_ne
      exact absurd hbq (Real.rpow_pos_of_pos (lt_of_le_of_ne hb (Ne.symm hb_ne)) q).ne'
    simp [ha0, hb0, Real.zero_rpow hp_pos.ne', Real.zero_rpow hq_pos.ne']
  by_cases hb0 : b = 0
  · have hbq : b ^ q = 0 := by rw [hb0]; exact Real.zero_rpow hq_pos.ne'
    exact absurd (heq ▸ hbq : a ^ p = 0)
      (Real.rpow_pos_of_pos (lt_of_le_of_ne ha (Ne.symm ha0)) p).ne'
  -- Both a > 0 and b > 0: use exp/log to compute deficit = 0
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  -- a^p = b^q implies p·log(a) = q·log(b)
  have hlog : p * Real.log a = q * Real.log b := by
    have := congr_arg Real.log heq
    rwa [Real.log_rpow ha_pos, Real.log_rpow hb_pos] at this
  -- Rewrite each piece via exp/log
  have ha_rpow : a ^ p = Real.exp (Real.log a * p) := Real.rpow_def_of_pos ha_pos p
  have hb_rpow : b ^ q = Real.exp (Real.log b * q) := Real.rpow_def_of_pos hb_pos q
  have hab : a * b = Real.exp (Real.log a + Real.log b) := by
    rw [Real.exp_add, Real.exp_log ha_pos, Real.exp_log hb_pos]
  rw [ha_rpow, hb_rpow, hab]
  -- Set t = log a * p = log b * q. Then all three exp terms become exp(t).
  set t := Real.log a * p with ht_def
  have ht2 : Real.log b * q = t := by linarith [mul_comm p (Real.log a)]
  rw [ht2]
  -- log a + log b = t/p + t/q = t·(1/p + 1/q) = t
  have hmix : Real.log a + Real.log b = t := by
    have hpq := conj_add_eq_mul hp hinv
    have h1 : q * Real.log b = p * Real.log a := by linarith [mul_comm p (Real.log a)]
    have h2 : (p + q) * Real.log a = p * q * Real.log a := by rw [hpq]
    have h3 : q * (Real.log a + Real.log b) = q * t := by nlinarith
    exact mul_left_cancel₀ hq_pos.ne' h3
  rw [hmix]
  -- Goal: exp(t)/p + exp(t)/q - exp(t) = 0
  have : Real.exp t / p + Real.exp t / q = Real.exp t := by
    have hpq := conj_add_eq_mul hp hinv
    field_simp
    nlinarith
  linarith

/-- Reverse direction: deficit = 0 → a^p = b^q via strict convexity of exp. -/
private theorem eq_of_youngDeficit_eq_zero {p q : ℝ} (hp : 1 < p)
    (hinv : 1 / p + 1 / q = 1) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hdef : youngDeficit p q a b = 0) : a ^ p = b ^ q := by
  unfold youngDeficit at hdef
  have hp_pos : (0 : ℝ) < p := by linarith
  have hq : 1 < q := conj_one_lt_q hp hinv
  have hq_pos : (0 : ℝ) < q := by linarith
  -- Zero cases
  by_cases ha0 : a = 0
  · rw [ha0, Real.zero_rpow hp_pos.ne'] at hdef ⊢
    simp only [zero_div, zero_add, zero_mul, sub_zero] at hdef
    exact (div_eq_zero_iff.mp hdef).elim Eq.symm (fun h => absurd h hq_pos.ne')
  by_cases hb0 : b = 0
  · rw [hb0, Real.zero_rpow hq_pos.ne'] at hdef ⊢
    simp only [zero_div, add_zero, mul_zero, sub_zero] at hdef
    exact (div_eq_zero_iff.mp hdef).elim id (fun h => absurd h hp_pos.ne')
  -- Both a, b > 0
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  -- Proof by contradiction using strict convexity of exp.
  -- Set x = p·log(a), y = q·log(b). Then exp(x) = a^p, exp(y) = b^q.
  -- (1/p)·exp(x) + (1/q)·exp(y) = a^p/p + b^q/q
  -- exp((1/p)·x + (1/q)·y) = exp(log a + log b) = a·b
  -- Strict convexity: LHS > RHS unless x = y, i.e., a^p = b^q.
  by_contra h_ne
  -- Use x = log a * p, y = log b * q (matching rpow_def_of_pos output)
  set x := Real.log a * p with hx_def
  set y := Real.log b * q with hy_def
  have hex : a ^ p = Real.exp x := Real.rpow_def_of_pos ha_pos p
  have hey : b ^ q = Real.exp y := Real.rpow_def_of_pos hb_pos q
  -- x ≠ y (since a^p ≠ b^q and exp is injective)
  have hxy : x ≠ y := by
    intro heq; apply h_ne; rw [hex, hey, heq]
  -- Strict convexity of exp: exp(t·x + (1-t)·y) < t·exp(x) + (1-t)·exp(y) when x ≠ y
  have hsc := strictConvexOn_exp.2 (Set.mem_univ x) (Set.mem_univ y) hxy
    (show (0 : ℝ) < 1 / p by positivity) (show (0 : ℝ) < 1 / q by positivity) hinv
  simp only [smul_eq_mul] at hsc
  -- Simplify LHS of hsc: 1/p * (log a * p) + 1/q * (log b * q) = log a + log b
  have hmix : 1 / p * x + 1 / q * y = Real.log a + Real.log b := by
    simp only [hx_def, hy_def]; field_simp
  rw [hmix, Real.exp_add, Real.exp_log ha_pos, Real.exp_log hb_pos] at hsc
  -- Simplify RHS: replace exp x, exp y with a^p, b^q
  rw [← hex, ← hey] at hsc
  -- hsc : a * b < 1/p * a^p + 1/q * b^q
  -- But hdef says a^p/p + b^q/q = a*b. Contradiction.
  have h1 : 1 / p * a ^ p = a ^ p / p := by ring
  have h2 : 1 / q * b ^ q = b ^ q / q := by ring
  linarith

/-- **Young's equality characterization**: For a, b ≥ 0 and conjugate p, q,
    the Young deficit is zero iff a^p = b^q.
    This is the key analytic fact (strict convexity of t^p). -/
theorem youngDeficit_eq_zero_iff {p q : ℝ} (hp : 1 < p) (hinv : 1 / p + 1 / q = 1)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    youngDeficit p q a b = 0 ↔ a ^ p = b ^ q :=
  ⟨eq_of_youngDeficit_eq_zero hp hinv ha hb, youngDeficit_eq_zero_of_eq hp hinv ha hb⟩

-- ============================================================================
-- Part VII: General Hölder Equality Characterization
-- ============================================================================

/-
The main structural theorem: Hölder equality reduces to pointwise Young equality.

Given f, g ≥ 0 and conjugate p, q, if we normalize to ‖f‖_p = ‖g‖_q = 1:
  ∑ fᵢgᵢ ≤ ∑ (fᵢ^p/p + gᵢ^q/q) = (∑fᵢ^p)/p + (∑gᵢ^q)/q = 1/p + 1/q = 1.

Equality ∑ fᵢgᵢ = 1 iff the sum of Young deficits is zero,
iff each Young deficit is zero (sum of nonneg = 0),
iff fᵢ^p = gᵢ^q for all i (by Young's equality case).

This generalizes the Cauchy-Schwarz proof technique:
  CS: sum of squared cross-terms = 0 → all cross-terms vanish
  Hölder: sum of Young deficits = 0 → all deficits vanish
-/

/-- Sum of Young deficits equals the total Hölder deficit:
    ∑(fᵢ^p/p + gᵢ^q/q - fᵢgᵢ) = (∑fᵢ^p)/p + (∑gᵢ^q)/q - ∑fᵢgᵢ. -/
theorem sum_youngDeficit {ι : Type*} (s : Finset ι) (f g : ι → ℝ) (p q : ℝ) :
    ∑ i ∈ s, youngDeficit p q (f i) (g i) =
      (∑ i ∈ s, f i ^ p) / p + (∑ i ∈ s, g i ^ q) / q -
      ∑ i ∈ s, f i * g i := by
  simp only [youngDeficit, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_div]

/-- **Sum of non-negative Young deficits equals zero iff each is zero.**
    This is the same "sum of nonneg = 0" technique used in the CS proof. -/
theorem sum_youngDeficit_eq_zero_iff {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    {p q : ℝ} (hp : 1 < p) (hinv : 1 / p + 1 / q = 1)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) :
    ∑ i ∈ s, youngDeficit p q (f i) (g i) = 0 ↔
    ∀ i ∈ s, youngDeficit p q (f i) (g i) = 0 := by
  constructor
  · intro hsum i hi
    have hnn : ∀ j ∈ s, 0 ≤ youngDeficit p q (f j) (g j) :=
      fun j hj => youngDeficit_nonneg hp hinv (hf j hj) (hg j hj)
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum i hi
  · intro hall
    exact Finset.sum_eq_zero fun i hi => hall i hi

/-- **Hölder equality implies pointwise power proportionality (normalized case).**
    If ∑fᵢ^p = 1, ∑gᵢ^q = 1, and ∑fᵢgᵢ = 1, then fᵢ^p = gᵢ^q for all i.

    Proof: ∑ Young deficits = 1/p + 1/q - 1 = 0, so each deficit = 0,
    so by Young's equality case, fᵢ^p = gᵢ^q. -/
theorem holder_eq_normalized_implies_power_prop {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    {p q : ℝ} (hp : 1 < p) (hinv : 1 / p + 1 / q = 1)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i)
    (hnorm_f : (∑ i ∈ s, f i ^ p) = 1) (hnorm_g : (∑ i ∈ s, g i ^ q) = 1)
    (heq : ∑ i ∈ s, f i * g i = 1) :
    ∀ i ∈ s, f i ^ p = g i ^ q := by
  -- The sum of Young deficits = 1/p + 1/q - 1 = 0
  have hsum : ∑ i ∈ s, youngDeficit p q (f i) (g i) = 0 := by
    rw [sum_youngDeficit, hnorm_f, hnorm_g, heq]
    have hp_pos : (0 : ℝ) < p := lt_trans one_pos hp
    have hq_pos : (0 : ℝ) < q := lt_trans one_pos (conj_one_lt_q hp hinv)
    have hp_ne : p ≠ 0 := ne_of_gt hp_pos
    have hq_ne : q ≠ 0 := ne_of_gt hq_pos
    rw [div_add_div _ _ hp_ne hq_ne]
    have hpq : p + q = p * q := conj_add_eq_mul hp hinv
    have : (1 * q + p * 1) / (p * q) - 1 = 0 := by
      rw [show 1 * q + p * 1 = p + q by ring, hpq, div_self (by positivity : p * q ≠ 0),
        sub_self]
    linarith
  -- Each deficit is 0 (sum of nonneg = 0)
  have hall := (sum_youngDeficit_eq_zero_iff s f g hp hinv hf hg).mp hsum
  -- Each deficit = 0 iff f_i^p = g_i^q
  intro i hi
  exact (youngDeficit_eq_zero_iff hp hinv (hf i hi) (hg i hi)).mp (hall i hi)

/-- **Hölder equality implies pointwise power proportionality (general case).**
    If equality holds in Hölder's inequality, then there exists c ≥ 0 such that
    fᵢ^p = c · gᵢ^q for all i.

    This reduces the general case to the normalized case by dividing
    f by the p-norm and g by the q-norm. -/
theorem holder_eq_implies_power_prop {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    {p q : ℝ} (hp : 1 < p) (hinv : 1 / p + 1 / q = 1)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i)
    (hFp : 0 < ∑ i ∈ s, f i ^ p) (hGq : 0 < ∑ i ∈ s, g i ^ q)
    (heq : ∑ i ∈ s, f i * g i =
      (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ i ∈ s, f i ^ p = c * g i ^ q := by
  -- The proportionality constant c = (∑f^p)/(∑g^q)
  use (∑ i ∈ s, f i ^ p) / (∑ i ∈ s, g i ^ q)
  refine ⟨div_nonneg (le_of_lt hFp) (le_of_lt hGq), ?_⟩
  -- Setup: normalization constants
  have hp_pos : (0 : ℝ) < p := by linarith
  have hq_pos : (0 : ℝ) < q := lt_trans one_pos (conj_one_lt_q hp hinv)
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  set Fp := ∑ j ∈ s, f j ^ p with hFp_def
  set Gq := ∑ j ∈ s, g j ^ q with hGq_def
  set a := Fp ^ (1 / p) with ha_def
  set b := Gq ^ (1 / q) with hb_def
  have ha_pos : 0 < a := rpow_pos_of_pos hFp _
  have hb_pos : 0 < b := rpow_pos_of_pos hGq _
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hb_ne : b ≠ 0 := ne_of_gt hb_pos
  -- Key cancellation: a^p = Fp and b^q = Gq
  have hap : a ^ p = Fp := by
    rw [ha_def, ← rpow_mul (le_of_lt hFp)]
    simp only [one_div, inv_mul_cancel₀ hp_ne, Real.rpow_one]
  have hbq : b ^ q = Gq := by
    rw [hb_def, ← rpow_mul (le_of_lt hGq)]
    simp only [one_div, inv_mul_cancel₀ hq_ne, Real.rpow_one]
  -- Normalization conditions
  have hnf : ∑ j ∈ s, (f j / a) ^ p = 1 := by
    have h : ∀ j ∈ s, (f j / a) ^ p = f j ^ p / a ^ p :=
      fun j hj => Real.div_rpow (hf j hj) (le_of_lt ha_pos) p
    rw [Finset.sum_congr rfl h, ← Finset.sum_div, hap, div_self (ne_of_gt hFp)]
  have hng : ∑ j ∈ s, (g j / b) ^ q = 1 := by
    have h : ∀ j ∈ s, (g j / b) ^ q = g j ^ q / b ^ q :=
      fun j hj => Real.div_rpow (hg j hj) (le_of_lt hb_pos) q
    rw [Finset.sum_congr rfl h, ← Finset.sum_div, hbq, div_self (ne_of_gt hGq)]
  have heq' : ∑ j ∈ s, (f j / a * (g j / b)) = 1 := by
    have h : ∀ j ∈ s, f j / a * (g j / b) = f j * g j / (a * b) :=
      fun _ _ => by ring
    rw [Finset.sum_congr rfl h, ← Finset.sum_div, heq,
      div_self (mul_ne_zero ha_ne hb_ne)]
  -- Apply normalized theorem
  intro i hi
  have key := holder_eq_normalized_implies_power_prop s
    (fun j => f j / a) (fun j => g j / b) hp hinv
    (fun j hj => div_nonneg (hf j hj) (le_of_lt ha_pos))
    (fun j hj => div_nonneg (hg j hj) (le_of_lt hb_pos))
    hnf hng heq' i hi
  -- key: (f i / a)^p = (g i / b)^q
  -- Unscale: f i^p / Fp = g i^q / Gq → f i^p = (Fp/Gq) · g i^q
  rw [Real.div_rpow (hf i hi) (le_of_lt ha_pos) p, hap,
    Real.div_rpow (hg i hi) (le_of_lt hb_pos) q, hbq] at key
  -- key: f i ^ p / Fp = g i ^ q / Gq
  rw [div_eq_div_iff (ne_of_gt hFp) (ne_of_gt hGq)] at key
  -- key: f i ^ p * Gq = g i ^ q * Fp
  field_simp
  linarith

/-- **Power proportionality implies Hölder equality** (reverse direction, normalized).
    If ∑fᵢ^p = 1, ∑gᵢ^q = 1, and fᵢ^p = gᵢ^q for all i, then ∑fᵢgᵢ = 1.
    Proof: each Young deficit is zero, so the total deficit is zero. -/
theorem power_prop_implies_holder_eq_normalized {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    {p q : ℝ} (hp : 1 < p) (hinv : 1 / p + 1 / q = 1)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i)
    (hnorm_f : (∑ i ∈ s, f i ^ p) = 1) (hnorm_g : (∑ i ∈ s, g i ^ q) = 1)
    (hprop : ∀ i ∈ s, f i ^ p = g i ^ q) :
    ∑ i ∈ s, f i * g i = 1 := by
  -- Each Young deficit is zero (since fᵢ^p = gᵢ^q)
  have hdef : ∀ i ∈ s, youngDeficit p q (f i) (g i) = 0 :=
    fun i hi => (youngDeficit_eq_zero_iff hp hinv (hf i hi) (hg i hi)).mpr (hprop i hi)
  -- Sum of deficits is zero
  have hsum : ∑ i ∈ s, youngDeficit p q (f i) (g i) = 0 :=
    Finset.sum_eq_zero fun i hi => hdef i hi
  -- sum_youngDeficit: total deficit = 1/p + 1/q - ∑fg = 0
  rw [sum_youngDeficit] at hsum
  rw [hnorm_f, hnorm_g] at hsum
  have hp_pos : (0 : ℝ) < p := by linarith
  have hq_pos : (0 : ℝ) < q := lt_trans one_pos (conj_one_lt_q hp hinv)
  linarith [div_add_div (1 : ℝ) (1 : ℝ) (ne_of_gt hp_pos) (ne_of_gt hq_pos),
    conj_add_eq_mul hp hinv,
    div_self (show p * q ≠ 0 by positivity)]

-- ============================================================================
-- Part VIII: Specialization — Recovering Cauchy-Schwarz from Hölder
-- ============================================================================

/-
When p = q = 2, the power proportionality condition fᵢ² = λ · gᵢ²
simplifies to fᵢ = ±√λ · gᵢ. With non-negative f, g, this is just
proportionality fᵢ = c · gᵢ, recovering our Part I result.
-/

/-- Cauchy-Schwarz as a special case of Hölder (p = q = 2):
    power proportionality fᵢ² = λ · gᵢ² implies proportionality. -/
theorem power_prop_sq_implies_prop {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i)
    {c : ℝ} (hc : 0 ≤ c) (hprop : ∀ i ∈ s, f i ^ 2 = c * g i ^ 2) :
    ∀ i ∈ s, f i = Real.sqrt c * g i := by
  intro i hi
  have h := hprop i hi
  have hfi := hf i hi
  have hgi := hg i hi
  have hsq_c : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc
  -- f_i^2 = c * g_i^2, so (f_i - √c · g_i)^2 = f_i^2 - 2·f_i·√c·g_i + c·g_i^2 = 0
  -- Since both f_i ≥ 0 and √c · g_i ≥ 0, this means f_i = √c · g_i
  have hcnn : 0 ≤ Real.sqrt c * g i := mul_nonneg (Real.sqrt_nonneg _) hgi
  nlinarith [sq_nonneg (f i - Real.sqrt c * g i), h, hsq_c]

-- ============================================================================
-- Part IX: Integral Hölder Equality (Measure Theory)
-- ============================================================================

/-
For measurable non-negative functions f, g on a measure space (α, μ),
equality in the integral Hölder inequality holds iff f^p and g^q are
proportional a.e. (almost everywhere).

The proof follows the same "sum of deficits = 0" technique, now applied
to the integral of the pointwise Young deficit:

  ∫ youngDeficit(f(x), g(x)) dμ = (∫ f^p dμ)/p + (∫ g^q dμ)/q - ∫ f·g dμ

With Hölder equality and normalized norms, this integral equals 0.
Since the integrand is a.e. non-negative (Young's inequality), each
pointwise deficit must be zero a.e. Young's equality case then gives
f(x)^p = g(x)^q a.e.

Key Mathlib ingredient: integral_eq_zero_iff_of_nonneg_ae
  (if ∫ h dμ = 0 and h ≥ 0 a.e. and h is integrable, then h = 0 a.e.)
-/

open MeasureTheory

/-- Integral of Young deficits equals the total Hölder deficit. -/
theorem integral_youngDeficit {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (f g : α → ℝ) (p q : ℝ)
    (hfp_int : Integrable (fun x => f x ^ p) μ)
    (hgq_int : Integrable (fun x => g x ^ q) μ)
    (hfg_int : Integrable (fun x => f x * g x) μ)
    (_ : 0 < p) (_ : 0 < q) :
    ∫ x, youngDeficit p q (f x) (g x) ∂μ =
      (∫ x, f x ^ p ∂μ) / p + (∫ x, g x ^ q ∂μ) / q -
      ∫ x, f x * g x ∂μ := by
  have h1 : Integrable (fun x => f x ^ p / p) μ := hfp_int.div_const p
  have h2 : Integrable (fun x => g x ^ q / q) μ := hgq_int.div_const q
  calc ∫ x, youngDeficit p q (f x) (g x) ∂μ
      = ∫ x, (f x ^ p / p + g x ^ q / q - f x * g x) ∂μ := by rw [show (fun x => youngDeficit p q (f x) (g x)) = (fun x => f x ^ p / p + g x ^ q / q - f x * g x) from rfl]
    _ = (∫ x, (f x ^ p / p + g x ^ q / q) ∂μ) - ∫ x, f x * g x ∂μ := integral_sub (h1.add h2) hfg_int
    _ = (∫ x, f x ^ p / p ∂μ + ∫ x, g x ^ q / q ∂μ) - ∫ x, f x * g x ∂μ := by rw [integral_add h1 h2]
    _ = (∫ x, f x ^ p ∂μ) / p + (∫ x, g x ^ q ∂μ) / q - ∫ x, f x * g x ∂μ := by simp [integral_div]

/-- **Integral Hölder equality: normalized case.**
    If ∫ f^p dμ = 1 and ∫ g^q dμ = 1 and ∫ f·g dμ = 1, then
    the Young deficit is zero a.e., giving f^p = g^q a.e.

    This is the measure-theoretic analogue of
    holder_eq_normalized_implies_power_prop. -/
theorem holder_eq_integral_normalized {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ}
    {p q : ℝ} (hp : 1 < p) (hinv : 1 / p + 1 / q = 1)
    (hf_nn : ∀ᵐ x ∂μ, 0 ≤ f x) (hg_nn : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hfp_int : Integrable (fun x => f x ^ p) μ)
    (hgq_int : Integrable (fun x => g x ^ q) μ)
    (hfg_int : Integrable (fun x => f x * g x) μ)
    (hdef_int : Integrable (fun x => youngDeficit p q (f x) (g x)) μ)
    (hnorm_f : ∫ x, f x ^ p ∂μ = 1) (hnorm_g : ∫ x, g x ^ q ∂μ = 1)
    (heq : ∫ x, f x * g x ∂μ = 1) :
    (fun x => f x ^ p) =ᵐ[μ] (fun x => g x ^ q) := by
  have hp_pos : (0 : ℝ) < p := by linarith
  have hq_pos : (0 : ℝ) < q := lt_trans one_pos (conj_one_lt_q hp hinv)
  -- Step 1: The integral of Young deficits = 1/p + 1/q - 1 = 0
  have hsum_zero : ∫ x, youngDeficit p q (f x) (g x) ∂μ = 0 := by
    rw [integral_youngDeficit f g p q hfp_int hgq_int hfg_int hp_pos hq_pos,
      hnorm_f, hnorm_g, heq]
    have hp_ne : p ≠ 0 := ne_of_gt hp_pos
    have hq_ne : q ≠ 0 := ne_of_gt hq_pos
    rw [div_add_div _ _ hp_ne hq_ne]
    have hpq : p + q = p * q := conj_add_eq_mul hp hinv
    rw [show (1 : ℝ) * q + p * 1 = p + q from by ring, hpq,
      div_self (by positivity : p * q ≠ 0), sub_self]
  -- Step 2: Young deficit is a.e. non-negative (by Young's inequality)
  have hdef_nn : ∀ᵐ x ∂μ, (0 : ℝ) ≤ youngDeficit p q (f x) (g x) := by
    filter_upwards [hf_nn, hg_nn] with x hfx hgx
    exact youngDeficit_nonneg hp hinv hfx hgx
  -- Step 3: Integral of a.e. nonneg = 0 → a.e. zero
  have hdef_ae_zero : (fun x => youngDeficit p q (f x) (g x)) =ᵐ[μ] (0 : α → ℝ) :=
    (integral_eq_zero_iff_of_nonneg_ae hdef_nn hdef_int).mp hsum_zero
  -- Step 4: Pointwise Young deficit = 0 → f^p = g^q (Young's equality case)
  filter_upwards [hdef_ae_zero, hf_nn, hg_nn] with x hx hfx hgx
  simp only [Pi.zero_apply] at hx
  exact (youngDeficit_eq_zero_iff hp hinv hfx hgx).mp hx

/-- **Integral Hölder equality: general case.**
    If equality holds in the integral Hölder inequality, then
    f^p and g^q are proportional a.e.: ∃ c ≥ 0, f^p = c · g^q a.e.

    This is the measure-theoretic analogue of
    holder_eq_implies_power_prop.

    Proof: normalize f by a = (∫ f^p)^{1/p} and g by b = (∫ g^q)^{1/q},
    apply the normalized result to get (f/a)^p = (g/b)^q a.e., then
    unscale to get f^p = (∫f^p / ∫g^q) · g^q a.e. -/
theorem holder_eq_integral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ}
    {p q : ℝ} (hp : 1 < p) (hinv : 1 / p + 1 / q = 1)
    (hf_nn : ∀ᵐ x ∂μ, 0 ≤ f x) (hg_nn : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hfp_int : Integrable (fun x => f x ^ p) μ)
    (hgq_int : Integrable (fun x => g x ^ q) μ)
    (hfg_int : Integrable (fun x => f x * g x) μ)
    (hFp : 0 < ∫ x, f x ^ p ∂μ) (hGq : 0 < ∫ x, g x ^ q ∂μ)
    (heq : ∫ x, f x * g x ∂μ =
      (∫ x, f x ^ p ∂μ) ^ (1 / p) * (∫ x, g x ^ q ∂μ) ^ (1 / q)) :
    ∃ c : ℝ, 0 ≤ c ∧ (fun x => f x ^ p) =ᵐ[μ] (fun x => c * g x ^ q) := by
  -- Setup: exponent positivity
  have hp_pos : (0 : ℝ) < p := by linarith
  have hq_pos : (0 : ℝ) < q := lt_trans one_pos (conj_one_lt_q hp hinv)
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  -- Normalization constants
  set Fp := ∫ x, f x ^ p ∂μ with hFp_def
  set Gq := ∫ x, g x ^ q ∂μ with hGq_def
  set a := Fp ^ (1 / p) with ha_def
  set b := Gq ^ (1 / q) with hb_def
  have ha_pos : 0 < a := rpow_pos_of_pos hFp _
  have hb_pos : 0 < b := rpow_pos_of_pos hGq _
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hb_ne : b ≠ 0 := ne_of_gt hb_pos
  -- Key cancellation: a^p = Fp and b^q = Gq
  have hap : a ^ p = Fp := by
    rw [ha_def, ← rpow_mul (le_of_lt hFp)]
    simp only [one_div, inv_mul_cancel₀ hp_ne, Real.rpow_one]
  have hbq : b ^ q = Gq := by
    rw [hb_def, ← rpow_mul (le_of_lt hGq)]
    simp only [one_div, inv_mul_cancel₀ hq_ne, Real.rpow_one]
  -- The proportionality constant c = Fp / Gq
  use Fp / Gq
  refine ⟨div_nonneg (le_of_lt hFp) (le_of_lt hGq), ?_⟩
  -- A.e. equalities for normalized functions (typed as EventuallyEq for .symm)
  have hdiv_f : (fun x => (f x / a) ^ p) =ᵐ[μ] (fun x => f x ^ p / a ^ p) := by
    filter_upwards [hf_nn] with x hfx
    exact Real.div_rpow hfx (le_of_lt ha_pos) p
  have hdiv_g : (fun x => (g x / b) ^ q) =ᵐ[μ] (fun x => g x ^ q / b ^ q) := by
    filter_upwards [hg_nn] with x hgx
    exact Real.div_rpow hgx (le_of_lt hb_pos) q
  have hdiv_fg : (fun x => (f x / a) * (g x / b)) =ᵐ[μ] (fun x => f x * g x / (a * b)) := by
    filter_upwards with x
    ring
  -- Integrability of normalized functions
  have hfp_norm_int : Integrable (fun x => (f x / a) ^ p) μ :=
    (hfp_int.div_const (a ^ p)).congr hdiv_f.symm
  have hgq_norm_int : Integrable (fun x => (g x / b) ^ q) μ :=
    (hgq_int.div_const (b ^ q)).congr hdiv_g.symm
  have hfg_norm_int : Integrable (fun x => (f x / a) * (g x / b)) μ :=
    (hfg_int.div_const (a * b)).congr hdiv_fg.symm
  -- Young deficit integrability for normalized functions
  have hdef_norm_int : Integrable (fun x => youngDeficit p q (f x / a) (g x / b)) μ := by
    simp only [youngDeficit]
    exact ((hfp_norm_int.div_const p).add (hgq_norm_int.div_const q)).sub hfg_norm_int
  -- Normalization conditions: ∫ (f/a)^p = 1, ∫ (g/b)^q = 1, ∫ (f/a)(g/b) = 1
  have hnf : ∫ x, (f x / a) ^ p ∂μ = 1 := by
    rw [integral_congr_ae hdiv_f, integral_div, hap, div_self (ne_of_gt hFp)]
  have hng : ∫ x, (g x / b) ^ q ∂μ = 1 := by
    rw [integral_congr_ae hdiv_g, integral_div, hbq, div_self (ne_of_gt hGq)]
  have heq' : ∫ x, (f x / a) * (g x / b) ∂μ = 1 := by
    rw [integral_congr_ae hdiv_fg, integral_div, heq,
      div_self (mul_ne_zero ha_ne hb_ne)]
  -- Non-negativity of normalized functions (a.e.)
  have hf_norm_nn : ∀ᵐ x ∂μ, 0 ≤ f x / a := by
    filter_upwards [hf_nn] with x hfx
    exact div_nonneg hfx (le_of_lt ha_pos)
  have hg_norm_nn : ∀ᵐ x ∂μ, 0 ≤ g x / b := by
    filter_upwards [hg_nn] with x hgx
    exact div_nonneg hgx (le_of_lt hb_pos)
  -- Apply normalized theorem: (f/a)^p =ᵃᵉ (g/b)^q
  have hnorm_result := holder_eq_integral_normalized hp hinv
    hf_norm_nn hg_norm_nn hfp_norm_int hgq_norm_int hfg_norm_int
    hdef_norm_int hnf hng heq'
  -- Unscale: f^p / Fp =ᵃᵉ g^q / Gq, hence f^p =ᵃᵉ (Fp/Gq) · g^q
  filter_upwards [hnorm_result, hdiv_f, hdiv_g] with x hx hdf hdg
  -- hx : (f x / a) ^ p = (g x / b) ^ q
  -- hdf : (f x / a) ^ p = f x ^ p / a ^ p
  -- hdg : (g x / b) ^ q = g x ^ q / b ^ q
  rw [hdf, hdg, hap, hbq] at hx
  -- hx : f x ^ p / Fp = g x ^ q / Gq
  rw [div_eq_div_iff (ne_of_gt hFp) (ne_of_gt hGq)] at hx
  -- hx : f x ^ p * Gq = g x ^ q * Fp
  -- Goal: f x ^ p = Fp / Gq * g x ^ q
  rw [div_mul_eq_mul_div]
  rw [eq_comm, div_eq_iff (ne_of_gt hGq)]
  linarith [mul_comm (g x ^ q) Fp]

end CauchySchwarzOQ03OQ01
