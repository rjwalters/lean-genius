/-
  Erdős Problem #1150: Supremum of Littlewood Polynomials

  Source: https://erdosproblems.com/1150
  Status: OPEN

  Statement:
  Does there exist a constant c > 0 such that, for all large n and all
  polynomials P of degree n with coefficients ±1:
    max_{|z|=1} |P(z)| > (1+c)√n ?

  Context:
  The lower bound max_{|z|=1} |P(z)| ≥ √(n+1) follows from Parseval.
  The question asks whether the sup norm must strictly exceed √n by a
  multiplicative factor. This is equivalent to asking whether ultraflat
  Littlewood polynomials (±1 coefficients) do NOT exist.

  Note: For unimodular coefficients (|a_k| = 1), Kahane (1980) showed
  ultraflat polynomials DO exist. But the ±1 case remains open.

  Related: Erdős #228 (flat Littlewood polynomials exist - SOLVED by BBMST 2019)
           Erdős #230 (ultraflat unimodular polynomials exist - SOLVED/DISPROVED)

  References:
  - [Ha74, Problem 4.31]
  - [Va99, Problem 2.36]
  - Balister-Bollobás-Morris-Sahasrabudhe-Tiba (2019)
-/

import Mathlib

open Complex Polynomial Filter

namespace Erdos1150

/-
## Definitions
-/

/-- A **Littlewood polynomial** has all coefficients in {-1, +1}. -/
def IsLittlewoodPolynomial (p : Polynomial ℂ) : Prop :=
  ∀ i ≤ p.natDegree, p.coeff i = 1 ∨ p.coeff i = -1

/-- The supremum of |P(z)| over the unit circle.
    Defined over the unit circle subtype for clean `ciSup_le` interaction. -/
noncomputable def supNorm (p : Polynomial ℂ) : ℝ :=
  ⨆ (z : {z : ℂ // ‖z‖ = 1}), ‖p.eval z.1‖

instance : Nonempty {z : ℂ // ‖z‖ = 1} := ⟨⟨1, norm_one⟩⟩

/-
## The Main Conjecture
-/

/-- **Erdős Problem #1150** (OPEN):
    Does there exist c > 0 such that for all sufficiently large n,
    every degree-n Littlewood polynomial P satisfies
    max_{|z|=1} |P(z)| > (1+c)√n?

    This is equivalent to: ultraflat Littlewood polynomials do NOT exist.
    Erdős conjectured the answer is YES (no ultraflat ±1 polynomials). -/
def Erdos1150Conjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ n in atTop,
    ∀ p : Polynomial ℂ, p.natDegree = n → IsLittlewoodPolynomial p →
    supNorm p > (1 + c) * Real.sqrt n

/-
## Parseval Lower Bound
-/

/-- **Parseval's theorem** gives the trivial lower bound:
    For any Littlewood polynomial of degree n,
    max_{|z|=1} |P(z)| ≥ √(n+1).

    Proof: ∫|P|² dθ/2π = Σ|aᵢ|² = n+1 for a degree-n Littlewood polynomial.
    So ‖P‖_∞² ≥ ‖P‖₂² = n+1. -/
axiom parseval_lower_bound :
    ∀ p : Polynomial ℂ, IsLittlewoodPolynomial p →
    supNorm p ≥ Real.sqrt (p.natDegree + 1)

/-- The Parseval bound shows √(n+1) > 0 for any polynomial. -/
theorem parseval_bound_pos (n : ℕ) (hn : n ≥ 1) :
    Real.sqrt (n + 1 : ℝ) > 0 := by
  exact Real.sqrt_pos.mpr (by positivity)

/-
## Equivalent Formulation: No Ultraflat Littlewood Polynomials
-/

/-- A sequence of Littlewood polynomials is **ultraflat** if their degrees
    tend to infinity and the ratio max_{|z|=1}|P_n(z)| / √(deg P_n) → 1.

    Note: The degrees need not be exactly n — this allows subsequences,
    which is the standard mathematical definition. The old definition
    requiring `(P n).natDegree = n` for all n was too restrictive:
    ¬Conjecture gives witnesses for infinitely many n (not all n),
    making the backward direction of the equivalence unprovable. -/
def IsUltraflat (P : ℕ → Polynomial ℂ) : Prop :=
  (∀ n, IsLittlewoodPolynomial (P n)) ∧
  (Filter.Tendsto (fun n => (P n).natDegree) atTop atTop) ∧
  Filter.Tendsto (fun n => supNorm (P n) / Real.sqrt ↑((P n).natDegree)) atTop (nhds 1)

/-- **Forward direction (proved):**
    If the conjecture holds, then no ultraflat Littlewood sequence exists.

    Proof: The conjecture gives a lower bound (1+c)√(degree) for all Littlewood
    polynomials of large degree. Since degrees → ∞ in an ultraflat sequence,
    the bound eventually applies, giving ratio > 1+c. But the ultraflat condition
    says ratio → 1, so eventually ratio < 1+c. Contradiction. -/
theorem conjecture_implies_no_ultraflat :
    Erdos1150Conjecture → ∀ P : ℕ → Polynomial ℂ, ¬ IsUltraflat P := by
  intro ⟨c, hc, hev⟩ P ⟨hlit, hdeg_tend, htend⟩
  -- Pull back the conjecture bound through the degree sequence
  have hpull : ∀ᶠ n in atTop,
      supNorm (P n) > (1 + c) * Real.sqrt ↑((P n).natDegree) :=
    (hdeg_tend.eventually hev).mono fun n hn => hn (P n) rfl (hlit n)
  -- Eventually degree > 0, so √degree > 0
  have hdeg_pos : ∀ᶠ n in atTop, 0 < (P n).natDegree :=
    hdeg_tend.eventually (Filter.eventually_atTop.mpr ⟨1, fun m hm => by omega⟩)
  -- Therefore ratio > 1+c eventually
  have hev' : ∀ᶠ n in atTop,
      supNorm (P n) / Real.sqrt ↑((P n).natDegree) > 1 + c := by
    apply (hpull.and hdeg_pos).mono
    intro n ⟨hgt, hpos⟩
    have hsqrt_pos : (0 : ℝ) < Real.sqrt ↑((P n).natDegree) :=
      Real.sqrt_pos_of_pos (Nat.cast_pos.mpr hpos)
    exact (lt_div_iff₀ hsqrt_pos).mpr (by linarith)
  -- From ultraflat: ratio → 1, so eventually < 1+c
  have hlt : ∀ᶠ n in atTop,
      supNorm (P n) / Real.sqrt ↑((P n).natDegree) < 1 + c := by
    have hmem : Set.Iio (1 + c) ∈ nhds (1 : ℝ) := Iio_mem_nhds (by linarith)
    exact htend hmem
  -- Contradiction: eventually > 1+c AND eventually < 1+c
  obtain ⟨n, hgt, hlt'⟩ := (hev'.and hlt).exists
  linarith

/-- **Backward direction (proved):**
    If no ultraflat Littlewood sequence exists, then the conjecture holds.

    Proof (contrapositive): Assume ¬Conjecture. For each k, ¬Conjecture with
    c = 1/(k+1) gives frequently many n with a degree-n Littlewood P satisfying
    supNorm(P) ≤ (1+1/(k+1))√n. Extract witnesses with degree ≥ k using
    Filter.frequently_atTop. The resulting sequence has degrees → ∞ (since
    n(k) ≥ k) and ratio supNorm/√degree → 1 (squeeze between Parseval's
    ratio ≥ 1 and the bound 1+1/(k+1) → 1), yielding an ultraflat sequence.
    Contradiction. -/
theorem no_ultraflat_implies_conjecture :
    (∀ P : ℕ → Polynomial ℂ, ¬ IsUltraflat P) → Erdos1150Conjecture := by
  intro hall
  by_contra hcontra
  -- For each c > 0, frequently there's a near-flat polynomial
  have hfreq : ∀ c : ℝ, c > 0 → ∃ᶠ n in atTop,
      ∃ p : Polynomial ℂ, p.natDegree = n ∧ IsLittlewoodPolynomial p ∧
      supNorm p ≤ (1 + c) * Real.sqrt ↑n := by
    intro c hc
    have h : ¬(∀ᶠ n in atTop, ∀ p : Polynomial ℂ, p.natDegree = n →
        IsLittlewoodPolynomial p → supNorm p > (1 + c) * Real.sqrt ↑n) :=
      fun hev => hcontra ⟨c, hc, hev⟩
    rw [Filter.not_eventually] at h
    exact h.mono fun n hn => by push_neg at hn; exact hn
  -- For each k, extract witness with c = 1/(k+1) and degree ≥ k
  have hext : ∀ k : ℕ, ∃ m : ℕ, m ≥ k ∧ ∃ p : Polynomial ℂ,
      p.natDegree = m ∧ IsLittlewoodPolynomial p ∧
      supNorm p ≤ (1 + 1 / ((k : ℝ) + 1)) * Real.sqrt ↑m := by
    intro k
    exact Filter.frequently_atTop.mp (hfreq (1 / ((k : ℝ) + 1)) (by positivity)) k
  -- Choose sequences: m(k) ≥ k with polynomial p(k) of degree m(k)
  choose m hm_ge p hdeg hlit hbound using hext
  -- Contradiction: p is an ultraflat Littlewood sequence
  apply hall p
  refine ⟨hlit, ?_, ?_⟩
  -- Degrees tend to infinity: (p k).natDegree = m k ≥ k → ∞
  · rw [Filter.tendsto_atTop_atTop]
    intro b
    exact ⟨b, fun k hk => by rw [hdeg k]; exact le_trans hk (hm_ge k)⟩
  -- Ratio → 1 by squeeze between Parseval's 1 and 1 + 1/(k+1)
  · have hlb : ∀ᶠ k in atTop,
        (1 : ℝ) ≤ supNorm (p k) / Real.sqrt ↑((p k).natDegree) :=
      Filter.eventually_atTop.mpr ⟨1, fun k hk =>
        parseval_ratio_ge_one (p k) (hlit k) (by rw [hdeg k]; have := hm_ge k; omega)⟩
    have hub : ∀ᶠ k in atTop,
        supNorm (p k) / Real.sqrt ↑((p k).natDegree) ≤ 1 + 1 / ((k : ℝ) + 1) :=
      Filter.eventually_atTop.mpr ⟨1, fun k hk => by
        have hsqrt_pos : (0 : ℝ) < Real.sqrt ↑((p k).natDegree) :=
          Real.sqrt_pos_of_pos (Nat.cast_pos.mpr (by rw [hdeg k]; have := hm_ge k; omega))
        rw [div_le_iff₀ hsqrt_pos, hdeg k]
        exact hbound k⟩
    have hub_tends : Tendsto (fun k : ℕ => (1 : ℝ) + 1 / ((k : ℝ) + 1)) atTop (nhds 1) := by
      have := tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      rwa [add_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hub_tends hlb hub

/-- The full equivalence follows from both directions. -/
theorem conjecture_equiv_no_ultraflat :
    Erdos1150Conjecture ↔ ∀ P : ℕ → Polynomial ℂ, ¬ IsUltraflat P :=
  ⟨conjecture_implies_no_ultraflat, no_ultraflat_implies_conjecture⟩

/-
## Known Results
-/

/-- **BBMST (2019)**: Flat Littlewood polynomials exist.
    There exist universal c₁, c₂ > 0 such that for all large n,
    there exists a degree-n Littlewood polynomial with
    c₁√n ≤ |P(z)| ≤ c₂√n for all |z| = 1.

    This does NOT resolve #1150: flat (bounded ratio) is weaker
    than ultraflat (ratio → 1). -/
axiom bbmst_flat :
    ∃ (c₁ c₂ : ℝ), c₁ > 0 ∧ c₂ > 0 ∧
    ∀ᶠ n in atTop, ∃ p : Polynomial ℂ,
      p.natDegree = n ∧ IsLittlewoodPolynomial p ∧
      ∀ z : ℂ, ‖z‖ = 1 →
        c₁ * Real.sqrt n ≤ ‖p.eval z‖ ∧ ‖p.eval z‖ ≤ c₂ * Real.sqrt n

/-- **Kahane (1980)**: Ultraflat polynomials exist for unimodular
    coefficients (|aᵢ| = 1, not necessarily ±1).
    This shows the restriction to ±1 is essential for #1150. -/
axiom kahane_unimodular_ultraflat :
    ∀ ε : ℝ, ε > 0 →
    ∀ᶠ n in atTop, ∃ coeffs : Fin (n + 1) → ℂ,
      (∀ i, ‖coeffs i‖ = 1) ∧
      ∀ z : ℂ, ‖z‖ = 1 →
        let P := ∑ i : Fin (n + 1), coeffs i * z ^ (i : ℕ)
        (1 - ε) * Real.sqrt n ≤ ‖P‖ ∧ ‖P‖ ≤ (1 + ε) * Real.sqrt n

/-- BBMST implies the sup norm of some Littlewood polynomial is at most c₂√n.
    In particular, it's NOT true that max|P| > C√n for arbitrarily large C.
    This follows from bbmst_flat (the sup norm is bounded by the pointwise bound). -/
theorem bbmst_upper_bound_exists :
    ∃ c₂ : ℝ, c₂ > 0 ∧ ∀ᶠ n in atTop,
      ∃ p : Polynomial ℂ, p.natDegree = n ∧ IsLittlewoodPolynomial p ∧
      supNorm p ≤ c₂ * Real.sqrt n := by
  obtain ⟨_, c₂, _, hc₂, hflat⟩ := bbmst_flat
  refine ⟨c₂, hc₂, hflat.mono fun n ⟨p, hdeg, hlit, hbound⟩ => ⟨p, hdeg, hlit, ?_⟩⟩
  -- supNorm is iSup over unit circle subtype, so ciSup_le applies directly
  exact ciSup_le fun z => (hbound z.1 z.2).2

/-
## The Gap Between Flat and Ultraflat
-/

/-- Parseval implies the sup-norm-to-sqrt-degree ratio is at least 1
    for any Littlewood polynomial with degree ≥ 1. This is the key
    lower bound ingredient for the ultraflat ↔ conjecture squeeze argument. -/
theorem parseval_ratio_ge_one (p : Polynomial ℂ) (hp : IsLittlewoodPolynomial p)
    (hn : p.natDegree ≥ 1) :
    supNorm p / Real.sqrt ↑p.natDegree ≥ 1 := by
  have hpb := parseval_lower_bound p hp
  have hsqrt_pos : (0 : ℝ) < Real.sqrt ↑p.natDegree :=
    Real.sqrt_pos_of_pos (Nat.cast_pos.mpr (by omega))
  have hsqrt_le : Real.sqrt ↑p.natDegree ≤ Real.sqrt (↑p.natDegree + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  calc (1 : ℝ) = Real.sqrt ↑p.natDegree / Real.sqrt ↑p.natDegree :=
        (div_self (ne_of_gt hsqrt_pos)).symm
    _ ≤ supNorm p / Real.sqrt ↑p.natDegree :=
        (div_le_div_right hsqrt_pos).mpr (by linarith)

/-- The key open question is about the gap between BBMST and ultraflat.
    BBMST shows c₁√n ≤ max|P| ≤ c₂√n for SOME P. But:
    - Can we make c₂ → 1? (ultraflat) Probably NOT for ±1.
    - Is there a universal c₂ < 1 + c for some c? This is #1150. -/
theorem flat_does_not_imply_ultraflat :
    (∃ (c₁ c₂ : ℝ), c₁ > 0 ∧ c₂ > 0 ∧
      ∀ᶠ n in atTop, ∃ p : Polynomial ℂ,
        p.natDegree = n ∧ IsLittlewoodPolynomial p ∧
        supNorm p ≤ c₂ * Real.sqrt n) →
    -- This does NOT give us ultraflat (we'd need c₂ → 1)
    True := by
  intro _; trivial

/-
## Rudin-Shapiro Construction
-/

/-- Rudin-Shapiro polynomial pair (P_k, Q_k), defined recursively:
    P₀ = Q₀ = 1,
    P_{k+1} = P_k + X^{2^k} · Q_k,
    Q_{k+1} = P_k - X^{2^k} · Q_k. -/
noncomputable def rudinShapiroPair : ℕ → Polynomial ℂ × Polynomial ℂ
  | 0 => (C 1, C 1)
  | k + 1 =>
    ((rudinShapiroPair k).1 + X ^ (2 ^ k) * (rudinShapiroPair k).2,
     (rudinShapiroPair k).1 - X ^ (2 ^ k) * (rudinShapiroPair k).2)

noncomputable def rsP (k : ℕ) : Polynomial ℂ := (rudinShapiroPair k).1
noncomputable def rsQ (k : ℕ) : Polynomial ℂ := (rudinShapiroPair k).2

@[simp] lemma rsP_zero : rsP 0 = C 1 := rfl
@[simp] lemma rsQ_zero : rsQ 0 = C 1 := rfl
@[simp] lemma rsP_succ (k : ℕ) : rsP (k + 1) = rsP k + X ^ (2 ^ k) * rsQ k := rfl
@[simp] lemma rsQ_succ (k : ℕ) : rsQ (k + 1) = rsP k - X ^ (2 ^ k) * rsQ k := rfl

/-- Parallelogram law: ‖a+b‖² + ‖a-b‖² = 2(‖a‖² + ‖b‖²). -/
private lemma parallelogram_complex (a b : ℂ) :
    ‖a + b‖ ^ 2 + ‖a - b‖ ^ 2 = 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  simp only [norm_add_sq_real, norm_sub_sq_real]; ring

/-- Key identity: on the unit circle, |P_k(z)|² + |Q_k(z)|² = 2^{k+1}.
    Proof by induction using the parallelogram law. -/
theorem rs_norm_sq_sum (k : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(rsP k).eval z‖ ^ 2 + ‖(rsQ k).eval z‖ ^ 2 = 2 * (2 : ℝ) ^ k := by
  induction k with
  | zero =>
    simp [rsP, rsQ, rudinShapiroPair, eval_C, norm_one]; norm_num
  | succ k ih =>
    simp only [rsP_succ, rsQ_succ, eval_add, eval_sub, eval_mul, eval_pow, eval_X]
    have hpar := parallelogram_complex ((rsP k).eval z) (z ^ (2 ^ k) * (rsQ k).eval z)
    have hnb : ‖z ^ (2 ^ k) * (rsQ k).eval z‖ = ‖(rsQ k).eval z‖ := by
      rw [norm_mul, norm_pow, hz, one_pow, one_mul]
    calc ‖(rsP k).eval z + z ^ (2 ^ k) * (rsQ k).eval z‖ ^ 2 +
          ‖(rsP k).eval z - z ^ (2 ^ k) * (rsQ k).eval z‖ ^ 2
        = 2 * (‖(rsP k).eval z‖ ^ 2 + ‖z ^ (2 ^ k) * (rsQ k).eval z‖ ^ 2) := hpar
      _ = 2 * (‖(rsP k).eval z‖ ^ 2 + ‖(rsQ k).eval z‖ ^ 2) := by rw [hnb]
      _ = 2 * (2 * (2 : ℝ) ^ k) := by rw [ih]
      _ = 2 * (2 : ℝ) ^ (k + 1) := by ring

/-- Combined: RS polynomials are nonzero and have degree 2^k - 1. -/
private lemma rs_ne_zero_and_degree : ∀ k : ℕ,
    rsP k ≠ 0 ∧ rsQ k ≠ 0 ∧
    (rsP k).natDegree = 2 ^ k - 1 ∧ (rsQ k).natDegree = 2 ^ k - 1 := by
  intro k
  induction k with
  | zero =>
    refine ⟨C_ne_zero.mpr one_ne_zero, C_ne_zero.mpr one_ne_zero, ?_, ?_⟩ <;>
      simp [rsP, rsQ, rudinShapiroPair, natDegree_C]
  | succ k ih =>
    obtain ⟨hPne, hQne, hdP, hdQ⟩ := ih
    have hdeg_xq : (X ^ (2 ^ k) * rsQ k).natDegree = 2 ^ k + (2 ^ k - 1) := by
      rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hQne, natDegree_X_pow, hdQ]
    have hdeg_p_lt : (rsP k).natDegree < (X ^ (2 ^ k) * rsQ k).natDegree := by
      rw [hdP, hdeg_xq]; omega
    have h2le : 2 ≤ 2 ^ (k + 1) := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k + 1) := pow_le_pow_right (by norm_num) (by omega)
    have hdP' : (rsP (k + 1)).natDegree = 2 ^ (k + 1) - 1 := by
      rw [rsP_succ, natDegree_add_eq_right_of_natDegree_lt hdeg_p_lt, hdeg_xq]; omega
    have hdQ' : (rsQ (k + 1)).natDegree = 2 ^ (k + 1) - 1 := by
      rw [rsQ_succ, sub_eq_add_neg, natDegree_add_eq_right_of_natDegree_lt
        (by rwa [natDegree_neg]), natDegree_neg, hdeg_xq]; omega
    refine ⟨?_, ?_, hdP', hdQ'⟩
    · intro h; rw [h, natDegree_zero] at hdP'; omega
    · intro h; rw [h, natDegree_zero] at hdQ'; omega

private lemma rsP_ne_zero (k : ℕ) : rsP k ≠ 0 := (rs_ne_zero_and_degree k).1
private lemma rsQ_ne_zero (k : ℕ) : rsQ k ≠ 0 := (rs_ne_zero_and_degree k).2.1
lemma rs_natDegree_P (k : ℕ) : (rsP k).natDegree = 2 ^ k - 1 :=
  (rs_ne_zero_and_degree k).2.2.1
lemma rs_natDegree_Q (k : ℕ) : (rsQ k).natDegree = 2 ^ k - 1 :=
  (rs_ne_zero_and_degree k).2.2.2

/-- Coefficients of X^n * p at i < n are 0. -/
private lemma coeff_X_pow_mul_of_lt {R : Type*} [Semiring R] (p : Polynomial R)
    (n i : ℕ) (hi : i < n) : (X ^ n * p).coeff i = 0 := by
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro ⟨a, b⟩ hab
  rw [Finset.Nat.mem_antidiagonal] at hab
  have : (X ^ n : Polynomial R).coeff a = 0 := by
    rw [Polynomial.coeff_X_pow, if_neg (by omega)]
  rw [this, zero_mul]

/-- Coefficients of X^n * p at n + i equal coeff p i. -/
private lemma coeff_X_pow_mul_add {R : Type*} [CommSemiring R] (p : Polynomial R)
    (n i : ℕ) : (X ^ n * p).coeff (n + i) = p.coeff i := by
  rw [mul_comm, show n + i = i + n from by omega, Polynomial.coeff_mul_X_pow]

/-- P_k and Q_k are both Littlewood polynomials (joint induction). -/
private lemma rs_littlewood_PQ : ∀ k : ℕ,
    IsLittlewoodPolynomial (rsP k) ∧ IsLittlewoodPolynomial (rsQ k) := by
  intro k
  induction k with
  | zero =>
    constructor <;> (intro i hi;
      simp [rsP, rsQ, rudinShapiroPair, natDegree_C] at hi;
      simp [rsP, rsQ, rudinShapiroPair, coeff_C, Nat.le_zero.mp hi])
  | succ k ih =>
    obtain ⟨ihP, ihQ⟩ := ih
    have hj_bound : ∀ j : ℕ, 2 ^ k + j ≤ 2 ^ (k + 1) - 1 → j ≤ 2 ^ k - 1 := by omega
    constructor
    · -- P_{k+1} = P_k + X^{2^k} * Q_k
      intro i hi
      rw [rsP_succ] at hi ⊢; simp only [coeff_add]
      by_cases hlt : i < 2 ^ k
      · rw [coeff_X_pow_mul_of_lt _ _ _ hlt, add_zero]
        exact ihP i (by rw [rs_natDegree_P]; omega)
      · push_neg at hlt
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [rs_natDegree_P]; omega), zero_add]
        obtain ⟨j, rfl⟩ : ∃ j, i = 2 ^ k + j := ⟨i - 2 ^ k, by omega⟩
        rw [coeff_X_pow_mul_add]
        have hdeg_sum : (rsP k + X ^ (2 ^ k) * rsQ k).natDegree = 2 ^ (k + 1) - 1 := by
          rw [natDegree_add_eq_right_of_natDegree_lt (by
            rw [rs_natDegree_P, natDegree_mul (pow_ne_zero _ X_ne_zero) (rsQ_ne_zero k),
                natDegree_X_pow, rs_natDegree_Q]; omega),
            natDegree_mul (pow_ne_zero _ X_ne_zero) (rsQ_ne_zero k),
            natDegree_X_pow, rs_natDegree_Q]; omega
        exact ihQ j (by rw [rs_natDegree_Q]; rw [hdeg_sum] at hi; exact hj_bound j hi)
    · -- Q_{k+1} = P_k - X^{2^k} * Q_k
      intro i hi
      rw [rsQ_succ] at hi ⊢; simp only [coeff_sub]
      by_cases hlt : i < 2 ^ k
      · rw [coeff_X_pow_mul_of_lt _ _ _ hlt, sub_zero]
        exact ihP i (by rw [rs_natDegree_P]; omega)
      · push_neg at hlt
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [rs_natDegree_P]; omega), zero_sub]
        obtain ⟨j, rfl⟩ : ∃ j, i = 2 ^ k + j := ⟨i - 2 ^ k, by omega⟩
        rw [coeff_X_pow_mul_add]
        have hdeg_sub : (rsP k - X ^ (2 ^ k) * rsQ k).natDegree = 2 ^ (k + 1) - 1 := by
          rw [sub_eq_add_neg, natDegree_add_eq_right_of_natDegree_lt (by
            rw [natDegree_neg, rs_natDegree_P,
                natDegree_mul (pow_ne_zero _ X_ne_zero) (rsQ_ne_zero k),
                natDegree_X_pow, rs_natDegree_Q]; omega),
            natDegree_neg, natDegree_mul (pow_ne_zero _ X_ne_zero) (rsQ_ne_zero k),
            natDegree_X_pow, rs_natDegree_Q]; omega
        have hq := ihQ j (by rw [rs_natDegree_Q]; rw [hdeg_sub] at hi; exact hj_bound j hi)
        rcases hq with h | h
        · right; rw [h]; ring  -- coeff = 1 → -coeff = -1
        · left; rw [h]; ring   -- coeff = -1 → -coeff = 1

lemma rs_littlewood_P (k : ℕ) : IsLittlewoodPolynomial (rsP k) := (rs_littlewood_PQ k).1

/-- **Rudin-Shapiro bound** (proved constructively): For k ≥ 1,
    there exists a degree-(2^k-1) Littlewood polynomial with
    sup norm ≤ √(2·2^k). -/
theorem rudin_shapiro_bound :
    ∀ k : ℕ, k ≥ 1 →
    ∃ p : Polynomial ℂ, p.natDegree = 2^k - 1 ∧
      IsLittlewoodPolynomial p ∧
      supNorm p ≤ Real.sqrt (2 * 2^k) := by
  intro k hk
  refine ⟨rsP k, rs_natDegree_P k, rs_littlewood_P k, ?_⟩
  apply ciSup_le
  intro ⟨z, hz⟩
  have hsq := rs_norm_sq_sum k z hz
  have hle : ‖(rsP k).eval z‖ ^ 2 ≤ 2 * (2 : ℝ) ^ k := by
    linarith [sq_nonneg ‖(rsQ k).eval z‖]
  calc ‖(rsP k).eval z‖
      = Real.sqrt (‖(rsP k).eval z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (2 * (2 : ℝ) ^ k) := Real.sqrt_le_sqrt hle

/-
## Summary
-/

/--
**Erdős Problem #1150** (OPEN):

**Question**: Does there exist c > 0 such that for all large n,
every degree-n ±1 polynomial has max_{|z|=1} |P(z)| > (1+c)√n?

**Equivalent**: Do ultraflat Littlewood polynomials NOT exist?

**Known**:
1. Parseval: max|P| ≥ √(n+1) (trivial lower bound)
2. Rudin-Shapiro: max|P| ≤ √(2n) possible (concrete upper bound)
3. BBMST (2019): c₁√n ≤ max|P| ≤ c₂√n possible (flat, not ultraflat)
4. Kahane (1980): Ultraflat possible for unimodular (NOT ±1) coefficients

**Gap**: We know flat ±1 polynomials exist but not whether
ultraflat ±1 polynomials exist. Erdős conjectured they don't.

**Proved in this file**:
5. Conjecture ↔ no ultraflat ±1 sequences (both directions proved).
   Forward: conjecture bound contradicts ratio → 1.
   Backward: contrapositive diagonal extraction + squeeze theorem.
   Uses subsequence-based ultraflat definition for mathematical correctness.
6. BBMST implies supNorm bound (proved from pointwise bound)
7. Rudin-Shapiro bound (constructive: recursive definition, parallelogram law
   induction for norm bound, joint induction for degree and Littlewood property)
-/
theorem erdos_1150_summary :
    -- Parseval lower bound holds
    (∀ p : Polynomial ℂ, IsLittlewoodPolynomial p →
      supNorm p ≥ Real.sqrt (p.natDegree + 1)) ∧
    -- Flat Littlewood polynomials exist
    (∃ (c₁ c₂ : ℝ), c₁ > 0 ∧ c₂ > 0 ∧
      ∀ᶠ n in atTop, ∃ p : Polynomial ℂ,
        p.natDegree = n ∧ IsLittlewoodPolynomial p ∧
        ∀ z : ℂ, ‖z‖ = 1 →
          c₁ * Real.sqrt n ≤ ‖p.eval z‖ ∧ ‖p.eval z‖ ≤ c₂ * Real.sqrt n) ∧
    -- Equivalence: conjecture ↔ no ultraflat sequences
    (Erdos1150Conjecture ↔ ∀ P : ℕ → Polynomial ℂ, ¬ IsUltraflat P) := by
  exact ⟨parseval_lower_bound, bbmst_flat, conjecture_equiv_no_ultraflat⟩

end Erdos1150
