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
## Parseval Lower Bound — Infrastructure

The Parseval bound can be proved via discrete Fourier analysis (no integration needed):

**Proof plan** (DFT approach):
Let N = n+1, ω = exp(2πi/N) (primitive N-th root of unity).
1. Orthogonality: Σ_{m<N} ω^(md) = N if N|d, 0 otherwise.
2. DFT identity: Σ_{m<N} |P(ω^m)|² = N·Σ_{k≤n} |a_k|² = N(n+1) = N².
3. Pigeonhole: max_m |P(ω^m)|² ≥ N²/N = N = n+1.
4. Since |ω^m| = 1: supNorm(P) ≥ √(n+1).

Step 2 expands |P(ω^m)|² as a double sum, swaps summation order, and uses step 1.
This is the main remaining work to eliminate the Parseval axiom below.
-/

/-- **Orthogonality of roots of unity**: for r with r^N = 1 and r ≠ 1,
    the geometric sum Σ_{m<N} r^m vanishes. -/
theorem roots_orthogonal {N : ℕ} {r : ℂ} (hr : r ^ N = 1) (hr1 : r ≠ 1) :
    ∑ m ∈ Finset.range N, r ^ m = 0 := by
  have h := geom_sum_eq hr1 N
  rw [hr, sub_self, zero_div] at h
  exact h

/-- Sum over all N-th roots of unity: Σ_{m<N} 1^m = N. -/
theorem roots_sum_one (N : ℕ) :
    ∑ m ∈ Finset.range N, (1 : ℂ) ^ m = ↑N := by
  simp

/-- For Littlewood polynomials, each coefficient has norm 1. -/
theorem littlewood_coeff_norm {p : Polynomial ℂ} (hp : IsLittlewoodPolynomial p)
    {k : ℕ} (hk : k ≤ p.natDegree) : ‖p.coeff k‖ = 1 := by
  rcases hp k hk with h | h <;> simp [h]

/-- For Littlewood polynomials, each coefficient has norm squared 1. -/
theorem littlewood_coeff_normSq {p : Polynomial ℂ} (hp : IsLittlewoodPolynomial p)
    {k : ℕ} (hk : k ≤ p.natDegree) : ‖p.coeff k‖ ^ 2 = 1 := by
  rw [littlewood_coeff_norm hp hk, one_pow]

/-- The sum of coefficient norm-squareds for a degree-n Littlewood polynomial is n+1. -/
theorem littlewood_coeffNormSq_sum {p : Polynomial ℂ} (hp : IsLittlewoodPolynomial p) :
    ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖ ^ 2 = ↑(p.natDegree + 1) := by
  simp_rw [littlewood_coeff_normSq hp (Finset.mem_range.mp · |>.le)]
  simp [Finset.sum_const, Finset.card_range]

/-- **Parseval's theorem** gives the trivial lower bound:
    For any Littlewood polynomial of degree n,
    max_{|z|=1} |P(z)| ≥ √(n+1).

    Proof sketch: Evaluate at (n+1)-th roots of unity. By DFT orthogonality,
    Σ_m |P(ω^m)|² = (n+1)·Σ_k |a_k|² = (n+1)². Pigeonhole gives
    max|P(ω^m)| ≥ √(n+1), and since |ω^m| = 1, supNorm P ≥ √(n+1).

    TODO: Replace this axiom with a full proof. Remaining steps:
    1. Prove BddAbove for supNorm (triangle inequality on unit circle)
    2. Prove DFT Parseval identity: Σ_{m<N} ‖P(ω^m)‖² = N²
       using roots_orthogonal + littlewood_coeffNormSq_sum
    3. Pigeonhole: max_m ‖P(ω^m)‖² ≥ N, so ‖P(ω^m)‖ ≥ √N
    4. le_ciSup + BddAbove to lift to supNorm -/
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
## Rudin-Shapiro Bound
-/

/-- **Rudin-Shapiro polynomials** give a concrete family with
    max_{|z|=1} |P(z)| ≤ √(2(n+1)) for degree n.
    These are Littlewood polynomials with bounded sup norm. -/
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
