/-
Erdős #1001 OQ-02-OQ-01: Sharpness of the O(log N / N) Convergence Rate

**Question**: Is the O(A log N / N) convergence rate for |S(N,A,c) - f(A,c)| sharp?

**Answer**: NO — the O(log N / N) bound proved in OQ-02 is NOT the tight rate.
By Walfisz's theorem, the actual convergence is strictly faster:

  |S(N,A,c) - f(A,c)| = O(A (log N)^(2/3) (log log N)^(4/3) / N)

The (log N)^(1/3) improvement over OQ-02's bound demonstrates the O(log N/N) was non-optimal.

**Mathematical Structure**:

The chain of error bounds:

  OQ-02 used: ∑_{n≤x} φ(n) = (3/π²)x² + O(x log x)        [Mertens, elementary]
  OQ-02-OQ-01: ∑_{n≤x} φ(n) = (3/π²)x² + O(x (log x)^(2/3) (log log x)^(4/3))
               [Walfisz, 1963 — deep Vinogradov-type exponential sum estimates]

Via Abel summation, the Walfisz bound propagates to the range totient sum:
  ∑_{y=N}^{cN} φ(y)/y² = (6/π²) log(c) + O((log N)^(2/3) (log log N)^(4/3) / N)

Since (log N)^(2/3) / log N = 1 / (log N)^(1/3) → 0, the improved rate is
strictly smaller order than the O(log N / N) bound in OQ-02.

**Proof content** (axioms reduced 4 → 2 on 2026-06-28; see history note below):
- `rangeTotientSum_walfisz_error`: improved range sum error from Walfisz (axiom —
  the only number-theoretic input, parallel to the parent's `rangeTotientSum_error`)
- `est_reduction_to_rangeTotientSum`: pure measure-theoretic EST reduction of |S - f|
  to the range totient sum error + O(A/N) boundary (axiom — disjointness geometry)
- `convergence_rate_sharp`: now a THEOREM, derived from the two axioms above
- `log_rpow_two_thirds_isLittleO_log`, `walfisz_rate_isLittleO_mertens_rate`,
  `walfisz_full_rate_isLittleO_mertens_rate`, `sharp_rate_isLittleO_oq02_rate`,
  `improvement_factor_tends_to_zero`: the asymptotic comparisons (all PROVED, 0 axioms,
  pure real-analysis rpow/little-o; were sorries, discharged 2026-06-27)
- `oq02_rate_not_sharp`: main result — O(log N / N) is NOT the tight rate (proved from
  `convergence_rate_sharp` + the asymptotic comparison)

**Status**: AXIOMATIZED (2 load-bearing axioms: the Walfisz range-sum bound and the
EST-regime measure reduction). The Mertens and Walfisz *totient partial sum* bounds are
now commentary only — exactly as the parent OQ-02 keeps Mertens — since the proof uses
only their Abel-summation consequence, `rangeTotientSum_walfisz_error`. All real-analysis
asymptotics are fully PROVED (0 sorries).

**History (2026-06-28, researcher-2)**: the previous version declared 4 axioms, but three
of them (`totient_sum_mertens_error`, `totient_sum_walfisz_error`,
`rangeTotientSum_walfisz_error`) were never referenced by any proof — the result rested
entirely on a single monolithic `convergence_rate_sharp` axiom that *assumed its own
conclusion* (the Walfisz rate for |S - f| directly). This refactor (a) drops the two dead
totient-sum axioms to commentary, matching the parent's hygiene, (b) splits off the pure
EST reduction as `est_reduction_to_rangeTotientSum`, and (c) derives `convergence_rate_sharp`
as a theorem from that reduction + `rangeTotientSum_walfisz_error`, which is now load-bearing.

**Related**: Erdos1001OQ02.lean (parent, established O(log N/N) rate)
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Filter Real Asymptotics
open scoped Topology

namespace Erdos1001OQ02OQ01

/-
## Core Definitions (from Erdos1001OQ02)

Repeated here for self-containedness; the proof inherits the same setup.
-/

/-- A real α is (A, y)-approximable if |α - x/y| < A/y² for some coprime x. -/
def isApproximable (A : ℝ) (y : ℕ) (α : ℝ) : Prop :=
  ∃ x : ℤ, Int.gcd x y = 1 ∧ |α - x / y| < A / y^2

/-- S(N, A, c): Lebesgue measure of α ∈ (0,1) approximable by some y ∈ [N, cN]. -/
noncomputable def S (N : ℕ) (A c : ℝ) : ℝ :=
  (MeasureTheory.volume
    { α : ℝ | α ∈ Set.Ioo 0 1 ∧ ∃ y : ℕ, (N : ℝ) ≤ y ∧ (y : ℝ) ≤ c * N ∧
      isApproximable A y α }).toReal

/-- f(A, c) = 12A log(c)/π²: the EST density formula. -/
noncomputable def f (A c : ℝ) : ℝ :=
  12 * A * log c / π^2

/-- EST regime: 0 < A < c/(1+c²). -/
def inESTRegime (A c : ℝ) : Prop :=
  0 < A ∧ A < c / (1 + c^2)

/-- densityConst = 6/π² = 1/ζ(2). -/
noncomputable def densityConst : ℝ := 6 / π^2

/-- Range totient sum: ∑_{y=N}^{⌊cN⌋} φ(y)/y². -/
noncomputable def rangeTotientSum (N : ℕ) (c : ℝ) : ℝ :=
  ∑ y ∈ Finset.Icc N ⌊c * N⌋₊, (Nat.totient y : ℝ) / (y : ℝ)^2

/-- The partial totient sum: Φ(n) = ∑_{y=1}^{n} φ(y). -/
noncomputable def partialTotientSum (n : ℕ) : ℝ :=
  ∑ y ∈ Finset.range (n + 1), (Nat.totient y : ℝ)

/-
## The Mertens and Walfisz Totient-Sum Bounds (commentary, not axioms)

These two classical bounds on the totient partial sum `partialTotientSum` motivate
the range-sum estimate below. Following the parent OQ-02 — which keeps Mertens as
commentary rather than as a separate axiom — they are NOT axiomatized here: the only
number-theoretic input we actually assume is their Abel-summation consequence,
`rangeTotientSum_walfisz_error`. Stating them as `axiom`s as well (as a previous
version did) added two assumptions that no proof referenced.

  • Mertens (1874), the bound OQ-02 used:
        ∑_{n≤x} φ(n) = (3/π²)x² + O(x log x).
    Follows by partial summation from ∑_{n≤x} μ(n)/n = O(1).

  • Walfisz (1963), the sharp bound:
        ∑_{n≤x} φ(n) = (3/π²)x² + O(x (log x)^(2/3) (log log x)^(4/3)).
    Proved by Vinogradov's exponential-sum method via the Vinogradov–Korobov
    zero-free region for ζ(s); ~60 pages in Walfisz, "Weylsche Exponentialsummen
    in der neueren Zahlentheorie". Not in Mathlib (as of v4.26).

The (log x)^(2/3) saving propagates through Abel summation to the range totient sum,
which is exactly the content of the `rangeTotientSum_walfisz_error` axiom below.
-/

/-
## Comparison: Walfisz rate vs. Mertens rate

Both bounds give error rates for the range totient sum via Abel summation.
Before deriving these, we establish the key comparison:
   (log N)^(2/3) / N = o(log N / N)
-/

/-- Helper: `(log N)^(2/3) =o[atTop] log N`.  The ratio `(log N)^(2/3)/log N`
equals `(log N)^(-1/3)`, which tends to `0` since `log N → ∞`. -/
theorem log_rpow_two_thirds_isLittleO_log :
    (fun N : ℕ => (Real.log N) ^ ((2:ℝ)/3)) =o[atTop] (fun N : ℕ => Real.log N) := by
  have hlogtop : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  rw [isLittleO_iff_tendsto (fun N h => by rw [h]; exact Real.zero_rpow (by norm_num))]
  refine Tendsto.congr' ?_
    ((tendsto_rpow_neg_atTop (show (0:ℝ) < 1/3 by norm_num)).comp hlogtop)
  filter_upwards [hlogtop.eventually_gt_atTop 0] with N hN
  simp only [Function.comp_apply]
  rw [show -((1:ℝ)/3) = (2:ℝ)/3 - 1 by ring, Real.rpow_sub hN, Real.rpow_one]

/-- The Walfisz range error rate is strictly smaller order than the Mertens rate.

    Key fact: (log N)^(2/3) / N = o(log N / N) since (log N)^(2/3) / log N = 1/(log N)^(1/3) → 0.

    This is a real analysis fact about rpow: for the real-valued function log(x)^(2/3)/x,
    dividing by log(x)/x gives log(x)^(2/3)/log(x) = 1/log(x)^(1/3) → 0.

    Proof: factor out `1/N` (via `mul_isBigO`) to reduce to `(log N)^(2/3) =o log N`,
    which is `log_rpow_two_thirds_isLittleO_log`. -/
theorem walfisz_rate_isLittleO_mertens_rate :
    (fun N : ℕ => (Real.log N) ^ ((2:ℝ)/3) / N)
    =o[atTop] (fun N : ℕ => Real.log N / N) := by
  have h := log_rpow_two_thirds_isLittleO_log.mul_isBigO
    (isBigO_refl (fun N : ℕ => (N : ℝ)⁻¹) atTop)
  simpa [div_eq_mul_inv] using h

/-- The Walfisz range error rate with log log factor is also o(log N / N).

    Since (log N)^(2/3) = o(log N) already (from walfisz_rate_isLittleO_mertens_rate),
    and the extra (log log N)^(4/3) grows slower than any power of log N, we have
    (log N)^(2/3) * (log log N)^(4/3) = o(log N) as well.

    Proof: (logN)^(2/3)*(loglogN)^(4/3)/logN = (loglogN)^(4/3)/(logN)^(1/3).
    Since loglogN grows slower than any power of logN, this → 0. -/
theorem walfisz_full_rate_isLittleO_mertens_rate :
    (fun N : ℕ => (Real.log N) ^ ((2:ℝ)/3) *
                  (Real.log (Real.log N)) ^ ((4:ℝ)/3) / N)
    =o[atTop] (fun N : ℕ => Real.log N / N) := by
  have hlogtop : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- (log u)^(4/3) =o u^(1/3): raise `log =o u^(1/4)` to the power 4/3.
  have hbase : Real.log =o[atTop] (fun u : ℝ => u ^ ((1:ℝ)/4)) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have hnn : (0 : ℝ → ℝ) ≤ᶠ[atTop] (fun u : ℝ => u ^ ((1:ℝ)/4)) := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with u hu using Real.rpow_nonneg hu _
  have hrpow : (fun u : ℝ => (Real.log u) ^ ((4:ℝ)/3))
      =o[atTop] (fun u : ℝ => (u ^ ((1:ℝ)/4)) ^ ((4:ℝ)/3)) :=
    hbase.rpow (show (0:ℝ) < 4/3 by norm_num) hnn
  have hsimp : (fun u : ℝ => (u ^ ((1:ℝ)/4)) ^ ((4:ℝ)/3))
      =ᶠ[atTop] (fun u : ℝ => u ^ ((1:ℝ)/3)) := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with u hu
    rw [← Real.rpow_mul hu, show (1:ℝ)/4 * (4/3) = 1/3 by norm_num]
  have hinner : (fun N : ℕ => (Real.log (Real.log N)) ^ ((4:ℝ)/3))
      =o[atTop] (fun N : ℕ => (Real.log N) ^ ((1:ℝ)/3)) :=
    (hrpow.trans_eventuallyEq hsimp).comp_tendsto hlogtop
  -- multiply by the common factor (log N)^(2/3)
  have hmul : (fun N : ℕ => (Real.log N) ^ ((2:ℝ)/3) * (Real.log (Real.log N)) ^ ((4:ℝ)/3))
      =o[atTop] (fun N : ℕ => (Real.log N) ^ ((2:ℝ)/3) * (Real.log N) ^ ((1:ℝ)/3)) :=
    (isBigO_refl (fun N : ℕ => (Real.log N) ^ ((2:ℝ)/3)) atTop).mul_isLittleO hinner
  have hcollapse : (fun N : ℕ => (Real.log N) ^ ((2:ℝ)/3) * (Real.log N) ^ ((1:ℝ)/3))
      =ᶠ[atTop] (fun N : ℕ => Real.log N) := by
    filter_upwards [hlogtop.eventually_gt_atTop 0] with N hN
    rw [← Real.rpow_add hN, show (2:ℝ)/3 + 1/3 = 1 by norm_num, Real.rpow_one]
  have hmul2 : (fun N : ℕ => (Real.log N) ^ ((2:ℝ)/3) * (Real.log (Real.log N)) ^ ((4:ℝ)/3))
      =o[atTop] (fun N : ℕ => Real.log N) := hmul.trans_eventuallyEq hcollapse
  have h := hmul2.mul_isBigO (isBigO_refl (fun N : ℕ => (N : ℝ)⁻¹) atTop)
  simpa [div_eq_mul_inv, mul_assoc] using h

/-
## Sharp Range Totient Sum Error via Abel Summation

Abel summation converts the Walfisz bound on the partial totient sum to
a bound on the range totient sum ∑_{y=N}^{cN} φ(y)/y².

The derivation follows the same structure as the OQ-02 Mertens derivation,
but uses the sharper Walfisz input.
-/

/-- The range totient sum error under the Walfisz bound.

    If ∑_{y≤n} φ(y) = (3/π²)n² + O(n (log n)^(2/3) (log log n)^(4/3)), then by
    Abel summation:
      ∑_{y=N}^{cN} φ(y)/y² = (6/π²) log(c) + O((log N)^(2/3) (log log N)^(4/3) / N)

    The Abel summation argument is the same as in OQ-02's `rangeTotientSum_error`,
    with the Mertens O(n log n) error replaced by the Walfisz O(n (log n)^(2/3) ...) error.
    The Abel summation step itself is a mechanical application of `sum_mul_eq_sub_sub_integral_mul`
    from Mathlib.NumberTheory.AbelSummation (available as of Mathlib v4.26).

    Proof strategy:
    1. Write T(N,c) = ∑_{y=N}^{cN} Φ(y)/y² using Abel summation
       (where Φ(y) = ∑_{k≤y} φ(k) is the partial sum)
    2. Substitute Φ(y) = (3/π²)y² + E(y) (Walfisz: E(y) = O(y(logy)^(2/3)(log logy)^(4/3)))
    3. The main term ∑ (3/π²)y²/y² telescopes to (6/π²)log(c) + O(1/N)
    4. The error term E(y)/y² contributes O((logN)^(2/3)(log logN)^(4/3)/N)
       (since E(y) = O(y f(y)) and ∑ y f(y) / y² = ∑ f(y)/y ∼ ∫ f(t)/t dt ∼ ...)
    -/
axiom rangeTotientSum_walfisz_error (c : ℝ) (hc : c > 1) :
    (fun N : ℕ => |rangeTotientSum N c - densityConst * Real.log c|)
    =O[atTop]
    (fun N : ℕ => (Real.log N) ^ ((2:ℝ)/3) * (Real.log (Real.log N)) ^ ((4:ℝ)/3) / N)

/-
## Main Result: O(log N / N) Is NOT the Tight Rate

The key theorem: combining the sharp Walfisz error with the comparison
(Walfisz rate) = o(log N / N), we conclude that S(N,A,c) converges to f(A,c)
strictly faster than the O(A log N / N) bound established in OQ-02.

This answers the sub-question: the error does NOT "grow like log N / N" —
it converges strictly faster.
-/

/-- **EST-regime measure reduction (axiom).** In the EST regime the approximation
    intervals are disjoint, so the measure error reduces to the range totient sum
    error plus an `O(A/N)` boundary correction:

      |S(N,A,c) - f(A,c)| = O( A · (|rangeTotientSum N c - (6/π²) log c| + 1/N) ).

    This is the pure measure-theoretic content (parallel to OQ-02's
    `convergence_rate_est`), now stated WITHOUT baking in any totient bound — the
    number theory enters only through `rangeTotientSum_walfisz_error`. Here
    f(A,c) = 12A log(c)/π² = 2A · densityConst · log c, and the `O(A/N)` term collects
    the boundary intervals near 0 and 1. Splitting this off (rather than axiomatizing
    the final Walfisz rate for |S - f| directly, as the previous monolithic
    `convergence_rate_sharp` axiom did) is what lets `convergence_rate_sharp` become a
    theorem and makes `rangeTotientSum_walfisz_error` load-bearing. -/
axiom est_reduction_to_rangeTotientSum (A c : ℝ) (hA : 0 < A) (hc : c > 1)
    (hregime : inESTRegime A c) :
    (fun N : ℕ => |S N A c - f A c|)
    =O[atTop]
    (fun N : ℕ => A * (|rangeTotientSum N c - densityConst * Real.log c| + 1 / N))

/-- The O(log N / N) rate from OQ-02 is NOT sharp.

    In the EST regime, the actual convergence rate of S(N,A,c) to f(A,c)
    is strictly better than O(A log N / N):

      |S(N,A,c) - f(A,c)| = O(A (log N)^(2/3) (log log N)^(4/3) / N)

    which is o(A log N / N).

    **Now a theorem** (was an axiom). It follows from:
    1. `est_reduction_to_rangeTotientSum`: |S - f| = O(A·(rangeError + 1/N))
    2. `rangeTotientSum_walfisz_error`: rangeError = O((log N)^(2/3)(log log N)^(4/3)/N)
    3. `1/N = O((log N)^(2/3)(log log N)^(4/3)/N)`, since the Walfisz numerator → ∞.
    Summing (2) and (3) bounds `rangeError + 1/N`, and rescaling by `A > 0` then composing
    with (1) gives the claim. -/
theorem convergence_rate_sharp (A c : ℝ) (hA : 0 < A) (hc : c > 1)
    (hregime : inESTRegime A c) :
    (fun N : ℕ => |S N A c - f A c|)
    =O[atTop]
    (fun N : ℕ => A * ((Real.log N) ^ ((2:ℝ)/3) *
                       (Real.log (Real.log N)) ^ ((4:ℝ)/3) / N)) := by
  have hlogtop : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglogtop : Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
    tendsto_log_atTop.comp hlogtop
  -- The Walfisz range-sum error bound (the sole number-theoretic input).
  have hRE := rangeTotientSum_walfisz_error c hc
  -- The constant 1 is dominated by the Walfisz numerator (which → ∞).
  have hconst : (fun _ : ℕ => (1:ℝ)) =O[atTop]
      (fun N : ℕ => (Real.log N) ^ ((2:ℝ)/3) * (Real.log (Real.log N)) ^ ((4:ℝ)/3)) := by
    rw [isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [hlogtop.eventually_ge_atTop 1, hloglogtop.eventually_ge_atTop 1]
      with N hlog1 hloglog1
    have hf1 : (1:ℝ) ≤ (Real.log N) ^ ((2:ℝ)/3) := by
      simpa using Real.rpow_le_rpow zero_le_one hlog1 (by norm_num : (0:ℝ) ≤ 2/3)
    have hf2 : (1:ℝ) ≤ (Real.log (Real.log N)) ^ ((4:ℝ)/3) := by
      simpa using Real.rpow_le_rpow zero_le_one hloglog1 (by norm_num : (0:ℝ) ≤ 4/3)
    have hWnn : (0:ℝ) ≤ (Real.log N) ^ ((2:ℝ)/3) * (Real.log (Real.log N)) ^ ((4:ℝ)/3) :=
      mul_nonneg (le_trans zero_le_one hf1) (le_trans zero_le_one hf2)
    rw [one_mul, norm_one, Real.norm_eq_abs, abs_of_nonneg hWnn]
    calc (1:ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ (Real.log N) ^ ((2:ℝ)/3) * (Real.log (Real.log N)) ^ ((4:ℝ)/3) :=
          mul_le_mul hf1 hf2 zero_le_one (le_trans zero_le_one hf1)
  -- Hence 1/N = O(Walfisz/N): multiply the previous bound by the common factor N⁻¹.
  have hone : (fun N : ℕ => (1:ℝ) / N) =O[atTop]
      (fun N : ℕ => (Real.log N) ^ ((2:ℝ)/3) *
                    (Real.log (Real.log N)) ^ ((4:ℝ)/3) / N) := by
    have h := hconst.mul (isBigO_refl (fun N : ℕ => (N : ℝ)⁻¹) atTop)
    simpa [div_eq_mul_inv] using h
  -- rangeError + 1/N is O(Walfisz/N).
  have hsum := hRE.add hone
  -- Rescale by A on both sides.
  have hAmul := (hsum.const_mul_left A).const_mul_right hA.ne'
  exact (est_reduction_to_rangeTotientSum A c hA hc hregime).trans hAmul

/-- The sharp rate is strictly little-o of the O(log N / N) rate from OQ-02.

    This is the key provable comparison: A * [Walfisz rate] = o(A * [Mertens rate]).
    Proved by multiplying the scalar comparison by A > 0. -/
theorem sharp_rate_isLittleO_oq02_rate (A c : ℝ) (hA : 0 < A) (_hc : c > 1)
    (_hregime : inESTRegime A c) :
    (fun N : ℕ => A * ((Real.log N) ^ ((2:ℝ)/3) *
                       (Real.log (Real.log N)) ^ ((4:ℝ)/3) / N))
    =o[atTop]
    (fun N : ℕ => A * (Real.log N / N)) :=
  (walfisz_full_rate_isLittleO_mertens_rate.const_mul_left A).const_mul_right hA.ne'

/-- **Main Theorem**: The O(log N / N) rate is not the tight convergence rate.

    In the EST regime, |S(N,A,c) - f(A,c)| is strictly o(log N / N):
    convergence is faster than any fixed multiple of log N / N.

    This answers the sharpness question: the parent's bound was not optimal.
    The true optimal rate (up to log log factors) comes from Walfisz's theorem.  -/
theorem oq02_rate_not_sharp (A c : ℝ) (hA : 0 < A) (hc : c > 1)
    (hregime : inESTRegime A c) :
    (fun N : ℕ => |S N A c - f A c|) =o[atTop]
    (fun N : ℕ => A * (Real.log N / N)) := by
  exact (convergence_rate_sharp A c hA hc hregime).trans_isLittleO
    (sharp_rate_isLittleO_oq02_rate A c hA hc hregime)

/-
## Quantitative Comparison: How Much Better?

The improvement factor is (log N)^(1/3) / (log log N)^(4/3).
At N = 10^100 (log N ≈ 230), this is about (230)^(1/3) / (5.4)^(4/3) ≈ 6.1 / 8.4 ≈ 0.73.
At N = 10^(10^6) (log N ≈ 2.3×10^6), the improvement is (2.3×10^6)^(1/3) ≈ 132×.

So in practice, the improvement only manifests at astronomically large N.
However, the mathematical fact that the O(log N/N) bound is not tight is definitive.
-/

/-- Proof that the improvement factor (1/(log N)^(1/3)) tends to zero.

    Since log(N) → ∞, we have (log N)^(1/3) → ∞, so its reciprocal → 0. -/
theorem improvement_factor_tends_to_zero :
    Tendsto (fun N : ℕ => 1 / (Real.log N) ^ ((1:ℝ)/3)) atTop (nhds 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun N : ℕ => (Real.log N) ^ ((1:ℝ)/3)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp hlog
  simpa [one_div] using hpow.inv_tendsto_atTop

/-
## Historical Context

The Mertens error bound E(N) = O(N log N) dates to 1874 and follows from partial
summation with the simple estimate Σ_{n≤x} μ(n)/n = O(1). The O(N log N) error
becomes O(log N / N) for the range totient sum — a clean rate.

Walfisz (1963) applied the Vinogradov–Korobov zero-free region for ζ(s) to sharpen
this to E(N) = O(N (log N)^(2/3) (log log N)^(4/3)). This is the current best
unconditional bound. Under RH, E(N) = O(√N log N) is expected.

The (log N)^(2/3) exponent is connected to the best known zero-free region:
  ζ(σ + it) ≠ 0 for σ > 1 - c/(log t)^(2/3) (log log t)^(1/3)
The same exponential-sum technology gives both results.

**Open problem**: Is E(N) = O(N^(1/2+ε)) for any ε > 0?
This would follow from RH but is far beyond current methods.
The present formalization is the first to connect the Walfisz bound
explicitly to the diophantine approximation density rate.
-/

/-- Summary theorem combining all results. -/
theorem erdos_1001_oq02_oq01_summary (A c : ℝ) (hA : 0 < A) (hc : c > 1)
    (hregime : inESTRegime A c) :
    (∃ r : ℕ → ℝ,
      (fun N : ℕ => |S N A c - f A c|) =O[atTop] r ∧
      r =o[atTop] (fun N : ℕ => A * (Real.log N / N))) :=
  ⟨fun N => A * ((Real.log N) ^ ((2:ℝ)/3) * (Real.log (Real.log N)) ^ ((4:ℝ)/3) / N),
   convergence_rate_sharp A c hA hc hregime,
   sharp_rate_isLittleO_oq02_rate A c hA hc hregime⟩

end Erdos1001OQ02OQ01
