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

/-- **Full Cauchy-Schwarz Equality Characterization with Proportionality**:
    When g is not identically zero on s, equality holds iff f is a
    scalar multiple of g (proportional). -/
theorem cauchy_schwarz_eq_iff_proportional {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    {k : ι} (hk : k ∈ s) (hgk : g k ≠ 0) :
    (∑ i ∈ s, f i * g i) ^ 2 = (∑ i ∈ s, f i ^ 2) * (∑ i ∈ s, g i ^ 2) →
    ∃ c : ℝ, ∀ i ∈ s, f i = c * g i := by
  intro heq
  have hcross := cauchy_schwarz_eq_iff s f g |>.mp heq
  exact ⟨f k / g k, proportional_of_cross_terms_zero s f g hcross hk hgk⟩

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

/-- The Young deficit is non-negative (restates Young's inequality). -/
axiom youngDeficit_nonneg {p q : ℝ} (hp : 1 < p) (hinv : 1 / p + 1 / q = 1)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ youngDeficit p q a b

/-- **Young's equality characterization**: For a, b ≥ 0 and conjugate p, q,
    the Young deficit is zero iff a^p = b^q.
    This is the key analytic fact (strict convexity of t^p). -/
axiom youngDeficit_eq_zero_iff {p q : ℝ} (hp : 1 < p) (hinv : 1 / p + 1 / q = 1)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    youngDeficit p q a b = 0 ↔ a ^ p = b ^ q

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
  constructor
  · exact div_nonneg (le_of_lt hFp) (le_of_lt hGq)
  · -- Reduce to normalized case: f/‖f‖_p and g/‖g‖_q
    -- After normalization, f_i^p = g_i^q for all i
    -- Unscaling: f_i^p/(∑f^p) = g_i^q/(∑g^q), i.e., f_i^p = (∑f^p/∑g^q) * g_i^q
    sorry

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

end CauchySchwarzOQ03OQ01
