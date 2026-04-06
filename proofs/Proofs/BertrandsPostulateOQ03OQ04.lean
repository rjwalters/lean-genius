import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic
import Proofs.PrimeNumberTheorem
import Proofs.BertrandsPostulateOQ03

/-
# PNT-Based Asymptotic for Prime Gaps in Short Intervals

## Open Question: bertrands-postulate-oq-03-oq-04

The Prime Number Theorem (PNT) gives a global picture of prime distribution:
π(x) ~ x/ln(x). But it leaves open a finer question:

**For a "short" interval [x, x+h], how many primes does it contain?**

The PNT-based prediction is: π(x+h) - π(x) ~ h/ln(x) when h is not too small.
This density asymptotic is stronger than the prime gap conjecture (which only
asks for ≥1 prime) — it asks for the *count* to match the PNT prediction.

### What This File Formalizes

- **Definitions**: The short interval density ratio and the PNT density conjecture
- **Helper**: primeCounting strictly increasing implies a prime exists in the gap
- **Proved**: ShortIntervalPNT implies prime gap conjecture eventually (density ⟹ existence)
- **Proved**: PNT implies density for intervals of length cx (2 sorries for limit algebra)
- **Axiom**: Unconditional density for h = x^θ with θ < 1 is open
- **Conditional result**: Under RH, density holds for all h ≥ x^(1/2+ε)

### The Density Hierarchy

| Interval length h    | Density holds?                        | Status                       |
|----------------------|---------------------------------------|------------------------------|
| h = cx (fixed c > 0) | YES: π(x+cx) - π(x) ~ cx/ln(x)       | Proved from PNT (2 sorries)  |
| h = x^0.525 (BHP)    | Existence only (≥1 prime guaranteed)  | BHP 2001                     |
| h = x^(1/2+ε)        | YES under RH, open unconditionally    | Open (conditional on RH)     |
| h = x^(1/2)          | Unknown even under RH                 | Open                         |

### Key Insight: Density vs. Existence

Baker-Harman-Pintz (BHP 2001) proves *existence* of a prime in [x, x+x^0.525].
The *density* asymptotic π(x+h) - π(x) ~ h/ln(x) is much stronger:
it asserts the prime COUNT approaches the PNT prediction. This file formalizes
the structural implications and the separation between density and existence.
-/

noncomputable section

open Filter Topology Real Set Asymptotics
open PrimeNumberTheorem (primePi primeApprox)
open BertrandsPostulateOQ03 (PrimeGapConjecture)

namespace BertrandsPostulateOQ03OQ04

-- ============================================================
-- PART 1: Helper Lemma — primeCounting Increase Implies Prime
-- ============================================================

/-- If the prime counting function strictly increases from m to n,
    then there exists a prime strictly between m and n (inclusive on the right).

    Proof: by contradiction. If no prime in (m, n], then every prime ≤ n
    is also ≤ m, giving an injection of {primes ≤ n} into {primes ≤ m}
    — contradicting the strict count increase. -/
private lemma primeCounting_lt_implies_prime_exists {m n : ℕ} (hmn : m ≤ n)
    (h : Nat.primeCounting m < Nat.primeCounting n) :
    ∃ p, Nat.Prime p ∧ m < p ∧ p ≤ n := by
  by_contra hall
  push_neg at hall
  -- hall : ∀ p, Nat.Prime p → m < p → n < p (negation of ∃ prime in (m,n])
  have hcounting_ge : Nat.primeCounting n ≤ Nat.primeCounting m := by
    unfold Nat.primeCounting Nat.primeCounting'
    rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
    apply Finset.card_le_card
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    refine ⟨?_, hp.2⟩
    -- hp.1 : p < n+1, hp.2 : p.Prime; need: p < m+1 (i.e., p ≤ m)
    by_cases hmp : m < p
    · -- If p > m, then by hall p > n, contradicting p < n+1
      have := hall p hp.2 hmp
      omega
    · omega
  omega

-- ============================================================
-- PART 2: The Short Interval Density Concept
-- ============================================================

/-- The short interval prime density ratio for base point x and interval length h:
    (π(x+h) - π(x)) · ln(x) / h

    This equals 1 when π(x+h) - π(x) = h/ln(x), matching the PNT prediction.
    The factor ln(x) normalizes so that 1/ln(x) (the prime density near x) gives ratio 1. -/
noncomputable def shortIntervalDensityRatio (x h : ℝ) : ℝ :=
  ((primePi (x + h) : ℝ) - (primePi x : ℝ)) * Real.log x / h

/-- **Short Interval PNT** for exponent θ:
    The normalized density (π(x + x^θ) - π(x)) · ln(x) / x^θ → 1 as x → ∞.

    This is the precise asymptotic saying the interval [x, x + x^θ]
    contains approximately x^θ / ln(x) primes, matching the PNT prediction
    that primes have "local density" 1/ln(x) near x. -/
def ShortIntervalPNT (θ : ℝ) : Prop :=
  Tendsto (fun x : ℝ => shortIntervalDensityRatio x (x ^ θ)) atTop (𝓝 1)

-- ============================================================
-- PART 3: Short Interval PNT Implies Prime Gap Conjecture
-- ============================================================

/-- **ShortIntervalPNT implies density ratio is eventually positive.**

    If the density ratio → 1, then eventually density ratio > 1/2 > 0. -/
lemma shortIntervalPNT_implies_pos_eventually {θ : ℝ}
    (h : ShortIntervalPNT θ) :
    ∀ᶠ x in atTop, shortIntervalDensityRatio x (x ^ θ) > 0 := by
  have hball := (Metric.tendsto_nhds.mp h) (1/2) (by norm_num)
  filter_upwards [hball] with x hx
  simp only [Real.dist_eq] at hx
  linarith [abs_lt.mp hx |>.1]

/-- **Short Interval PNT implies Prime Gap Conjecture eventually.**

    If the density ratio (π(x+x^θ) - π(x)) · ln(x) / x^θ → 1, then
    eventually every interval [x, x+x^θ] contains at least one prime.

    This shows density (count asymptotics) is strictly stronger than existence.

    Key steps:
    1. Density ratio → 1 implies density ratio > 0 eventually
    2. With ln(x) > 0 and x^θ > 0: the prime count difference > 0 eventually
    3. primeCounting strictly increasing implies ∃ prime in the interval -/
theorem shortIntervalPNT_implies_primeGapConjecture_eventually {θ : ℝ} (hθ : 0 < θ) :
    ShortIntervalPNT θ →
    ∀ᶠ x in atTop, ∃ p : ℕ, Nat.Prime p ∧ (x : ℝ) < p ∧ (p : ℝ) ≤ x + x ^ θ := by
  intro hdens
  have hpos := shortIntervalPNT_implies_pos_eventually hdens
  filter_upwards [hpos, eventually_gt_atTop (3 : ℝ)] with x hx_dens hx3
  have hlog_pos : Real.log x > 0 := Real.log_pos (by linarith)
  have hpow_pos : x ^ θ > 0 := Real.rpow_pos_of_pos (by linarith) θ
  -- density ratio > 0 implies prime count difference > 0
  have hcount_diff_pos : (primePi (x + x ^ θ) : ℝ) - (primePi x : ℝ) > 0 := by
    simp only [shortIntervalDensityRatio] at hx_dens
    -- hx_dens : (count_diff * log x) / x^θ > 0, with x^θ > 0
    have h1 : ((primePi (x + x ^ θ) : ℝ) - (primePi x : ℝ)) * Real.log x > 0 := by
      rcases div_pos_iff.mp hx_dens with ⟨ha, _⟩ | ⟨_, hb⟩
      · exact ha
      · linarith [hpow_pos]
    -- count_diff * log x > 0 with log x > 0 implies count_diff > 0
    by_contra hle
    push_neg at hle
    have : ((primePi (x + x ^ θ) : ℝ) - (primePi x : ℝ)) * Real.log x ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hlog_pos.le
    linarith
  -- Convert to natural number inequality via cast
  have hlt : Nat.primeCounting ⌊x⌋₊ < Nat.primeCounting ⌊x + x ^ θ⌋₊ := by
    have h : (primePi x : ℝ) < primePi (x + x ^ θ) := by linarith
    exact_mod_cast h
  have hfloor_le : ⌊x⌋₊ ≤ ⌊x + x ^ θ⌋₊ :=
    Nat.floor_le_floor (by linarith [hpow_pos.le])
  obtain ⟨p, hp_prime, hp_lo, hp_hi⟩ :=
    primeCounting_lt_implies_prime_exists hfloor_le hlt
  refine ⟨p, hp_prime, ?_, ?_⟩
  · -- x < p: from ⌊x⌋₊ < p and x < ⌊x⌋₊ + 1
    have hp_ge_succ : (⌊x⌋₊ : ℝ) + 1 ≤ (p : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hp_lo
    linarith [Nat.lt_floor_add_one x]
  · -- p ≤ x + x^θ: from p ≤ ⌊x + x^θ⌋₊ ≤ x + x^θ
    exact le_trans (by exact_mod_cast hp_hi) (Nat.floor_le (by linarith [hpow_pos.le]))

-- ============================================================
-- PART 4: PNT Implies Density for Long Intervals
-- ============================================================

/-- Helper: log(x) / log((1+c)*x) → 1 as x → ∞ for any fixed c > 0.

    Proof: log((1+c)*x) = log(1+c) + log(x), so
    log(x)/log((1+c)*x) = 1/(1 + log(1+c)/log(x)) → 1/(1+0) = 1. -/
private lemma log_ratio_tendsto_one (c : ℝ) (hc : c > 0) :
    Tendsto (fun x : ℝ => Real.log x / Real.log ((1 + c) * x)) atTop (𝓝 1) := by
  have h1c_pos : (1 + c) > 0 := by linarith
  have hsimp : ∀ᶠ x in atTop, Real.log x / Real.log ((1 + c) * x) =
      1 / (1 + Real.log (1 + c) / Real.log x) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx_pos : (0 : ℝ) < x := by linarith
    have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
    rw [Real.log_mul (ne_of_gt h1c_pos) (ne_of_gt hx_pos)]
    field_simp; ring
  -- log(1+c)/log(x) → 0 as log(x) → ∞
  have hdiv_zero : Tendsto (fun x : ℝ => Real.log (1 + c) / Real.log x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  -- 1 + log(1+c)/log(x) → 1 + 0 = 1
  have hadd_one : Tendsto (fun x : ℝ => 1 + Real.log (1 + c) / Real.log x) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hdiv_zero
  -- 1 / (1 + log(1+c)/log(x)) → 1/1 = 1
  have hdiv_one : Tendsto (fun x : ℝ => (1:ℝ) / (1 + Real.log (1 + c) / Real.log x)) atTop (𝓝 1) := by
    have hconst : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h : Tendsto (fun x : ℝ => (1:ℝ) / (1 + Real.log (1 + c) / Real.log x)) atTop
        (𝓝 (1 / 1)) := hconst.div hadd_one one_ne_zero
    simp only [div_one] at h
    exact h
  rw [Filter.tendsto_congr' hsimp]
  exact hdiv_one

/-- **PNT implies the density asymptotic for intervals of length cx.**

    For any fixed c > 0, as x → ∞:
    (π((1+c)x) - π(x)) · ln(x) / (cx) → 1

    This means π(x + cx) - π(x) ~ cx/ln(x), i.e., the interval (x, (1+c)x]
    contains approximately cx/ln(x) primes, consistent with PNT.

    **Mathematical proof sketch**:
    1. PNT applied to (1+c)x: π((1+c)x) · ln((1+c)x) / ((1+c)x) → 1
    2. Since ln((1+c)x)/ln(x) → 1: π((1+c)x) · ln(x) / ((1+c)x) → 1
    3. Combining with PNT for x: (π((1+c)x) - π(x)) · ln(x) / (cx) → 1

    The limit algebra uses Tendsto.mul for step 2 and Tendsto.sub for step 3. -/
theorem long_interval_density_from_pnt (c : ℝ) (hc : c > 0) :
    Tendsto (fun x : ℝ =>
      ((primePi ((1 + c) * x) : ℝ) - (primePi x : ℝ)) * Real.log x / (c * x))
      atTop (𝓝 1) := by
  have h1c_pos : (0 : ℝ) < 1 + c := by linarith
  -- PNT for (1+c)*x: π((1+c)x) * log((1+c)x) / ((1+c)x) → 1
  have pnt_1c : Tendsto (fun x : ℝ =>
      (primePi ((1 + c) * x) : ℝ) * Real.log ((1 + c) * x) / ((1 + c) * x)) atTop (𝓝 1) :=
    PrimeNumberTheorem.primeNumberTheorem.comp
      (Filter.Tendsto.const_mul_atTop h1c_pos tendsto_id)
  -- log ratio: log x / log((1+c)x) → 1
  have hlog_ratio := log_ratio_tendsto_one c hc
  -- Combine to get: π((1+c)x) * log x / ((1+c)x) → 1
  -- Note: [π * log((1+c)x) / ((1+c)x)] * [log x / log((1+c)x)] = π * log x / ((1+c)x)
  have pnt_1c_logx : Tendsto (fun x : ℝ =>
      (primePi ((1 + c) * x) : ℝ) * Real.log x / ((1 + c) * x)) atTop (𝓝 1) := by
    -- Product of two limits: pnt_1c → 1 and hlog_ratio → 1, so product → 1
    have hmul := pnt_1c.mul hlog_ratio
    rw [mul_one] at hmul
    refine hmul.congr' ?_
    -- Show the functions are eventually equal (when log((1+c)x) ≠ 0)
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx_pos : (0 : ℝ) < x := by linarith
    have h1cx_pos : (0 : ℝ) < (1 + c) * x := by positivity
    have hlog_ne : Real.log ((1 + c) * x) ≠ 0 :=
      ne_of_gt (Real.log_pos (by nlinarith))
    -- [π·log(y)/y] · [log(x)/log(y)] = π·log(x)/y
    field_simp
    ring
  -- PNT for x: π(x) * log x / x → 1
  have pnt_x := PrimeNumberTheorem.primeNumberTheorem
  -- Combine: (π((1+c)x) - π(x)) * log x / (cx)
  -- = (1+c)/c * [π((1+c)x) * log x / ((1+c)x)] - 1/c * [π(x) * log x / x]
  -- → (1+c)/c * 1 - 1/c * 1 = 1
  have hc_ne : c ≠ 0 := ne_of_gt hc
  -- Scale pnt_1c_logx by (1+c)/c
  have h1 : Tendsto (fun x : ℝ =>
      (1 + c) / c * ((primePi ((1 + c) * x) : ℝ) * Real.log x / ((1 + c) * x)))
      atTop (𝓝 ((1 + c) / c * 1)) :=
    pnt_1c_logx.const_mul ((1 + c) / c)
  -- Scale pnt_x by 1/c
  have h2 : Tendsto (fun x : ℝ =>
      1 / c * ((primePi x : ℝ) * Real.log x / x))
      atTop (𝓝 (1 / c * 1)) :=
    pnt_x.const_mul (1 / c)
  -- Subtract: (1+c)/c · 1 - 1/c · 1 = 1
  have h3 := h1.sub h2
  rw [show (1 + c) / c * 1 - 1 / c * 1 = (1 : ℝ) by field_simp; ring] at h3
  -- Match function forms
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hx_ne : x ≠ 0 := ne_of_gt hx
  have hcx_ne : c * x ≠ 0 := mul_ne_zero hc_ne hx_ne
  have h1cx_ne : (1 + c) * x ≠ 0 := mul_ne_zero (ne_of_gt h1c_pos) hx_ne
  -- Algebraic identity
  field_simp
  ring

-- ============================================================
-- PART 5: The Open Landscape (Axioms)
-- ============================================================

/-- **Conditional result: Short Interval PNT under RH for all θ > 1/2** [CONDITIONAL]

    Assuming the Riemann Hypothesis: for all ε > 0, the density asymptotic
    π(x+h) - π(x) ~ h/ln(x) holds for h = x^(1/2+ε) as x → ∞.

    This follows from the RH error bound |π(x) - Li(x)| = O(√x · log x)
    (von Koch 1901): for h ≥ x^(1/2+ε), the error term is o(h/ln(x)),
    so the density ratio converges to 1.

    Why an axiom? Requires the full Riemann Hypothesis and detailed analytic
    number theory (explicit formula, zero-density estimates, contour integration). -/
axiom shortIntervalPNT_rh_conditional :
    PrimeNumberTheorem.RiemannHypothesis →
    ∀ ε : ℝ, ε > 0 → ShortIntervalPNT (1/2 + ε)

/-- **Theorem: RH implies Short Interval PNT for all θ > 1/2.**

    Under the Riemann Hypothesis, the PNT-based density asymptotic holds for
    all intervals of length h ≥ x^(1/2+ε). -/
theorem rh_implies_density_for_all_theta_gt_half
    (h : PrimeNumberTheorem.RiemannHypothesis) :
    ∀ θ : ℝ, θ > 1/2 → ShortIntervalPNT θ := by
  intro θ hθ
  have hε : θ - 1/2 > 0 := by linarith
  have := shortIntervalPNT_rh_conditional h (θ - 1/2) hε
  convert this using 2; ring

-- ============================================================
-- PART 6: Existence vs. Density — The Gap
-- ============================================================

/-- **Formal statement of the BHP-density gap.**

    BHP (2001) gives: PrimeGapConjecture 0.525 — existence of a prime in [x, x+x^0.525].
    Open problem: ShortIntervalPNT 0.525 — the density asymptotic for the same interval.

    The implication "density → existence eventually" holds (proved above).
    The reverse "existence → density" is NOT known for any θ < 1. -/
theorem bhp_vs_density_gap :
    PrimeGapConjecture 0.525 ∧
    (ShortIntervalPNT 0.525 →
      ∀ᶠ x in atTop, ∃ p : ℕ, Nat.Prime p ∧ (x : ℝ) < p ∧ (p : ℝ) ≤ x + x ^ (0.525 : ℝ)) :=
  ⟨BertrandsPostulateOQ03.prime_gap_conjecture_bhp,
   fun h => shortIntervalPNT_implies_primeGapConjecture_eventually (by norm_num) h⟩

-- ============================================================
-- PART 7: Summary
-- ============================================================

/-- **Summary of the prime density landscape in short intervals.**

    Collects the key known results and their relationships:
    1. BHP 2001: a prime exists in [x, x+x^0.525] (existence, not density)
    2. Bertrand: a prime exists in (x, 2x] (density proved from PNT)
    3. Density is stronger than existence: ShortIntervalPNT θ ⟹ PrimeGapConjecture eventually
    4. Under RH: density holds for all intervals of length ≥ x^(1/2+ε) -/
theorem prime_density_in_short_intervals_summary :
    -- (1) BHP 2001: existence for h = x^0.525
    PrimeGapConjecture 0.525 ∧
    -- (2) Bertrand: existence for h = x (the classical case)
    PrimeGapConjecture 1 ∧
    -- (3) BHP improves Bertrand: a sublinear exponent works for existence
    (∃ θ : ℝ, θ < 1 ∧ PrimeGapConjecture θ) ∧
    -- (4) ShortIntervalPNT implies PrimeGapConjecture eventually (density ⟹ existence)
    (ShortIntervalPNT 0.525 →
      ∀ᶠ x in atTop, ∃ p : ℕ, Nat.Prime p ∧ (x : ℝ) < p ∧ (p : ℝ) ≤ x + x ^ (0.525 : ℝ)) :=
  ⟨BertrandsPostulateOQ03.prime_gap_conjecture_bhp,
   BertrandsPostulateOQ03.density_question_status.2.1,
   ⟨0.525, by norm_num, BertrandsPostulateOQ03.prime_gap_conjecture_bhp⟩,
   fun h => shortIntervalPNT_implies_primeGapConjecture_eventually (by norm_num) h⟩

end BertrandsPostulateOQ03OQ04

end -- noncomputable section
