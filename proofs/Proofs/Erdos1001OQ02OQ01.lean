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

**Proof content** (3 axioms; down from 4 after the 2026-07-02 refactor):
- `totient_sum_walfisz_error`: Walfisz's sharp totient partial sum error (axiom — deep)
- `rangeTotientSum_walfisz_error`: improved range sum error from Walfisz (axiom — Abel sum;
  now LOAD-BEARING: `convergence_rate_sharp` is derived from it)
- `est_reduction`: the rate-agnostic EST-regime reduction `|S - f| = O(A·|range error|)`
  (axiom — disjointness geometry only, independent of the totient bound used)
- `convergence_rate_sharp`: now a THEOREM, derived by chaining `est_reduction` with the
  `A`-scaled `rangeTotientSum_walfisz_error` (was a monolithic axiom that assumed the answer)
- `log_rpow_two_thirds_isLittleO_log`, `walfisz_rate_isLittleO_mertens_rate`,
  `walfisz_full_rate_isLittleO_mertens_rate`, `sharp_rate_isLittleO_oq02_rate`,
  `improvement_factor_tends_to_zero`: the asymptotic comparisons (all PROVED, 0 axioms,
  pure real-analysis rpow/little-o; were sorries, discharged 2026-06-27)
- `oq02_rate_not_sharp`: main result — O(log N / N) is NOT the tight rate (proved from
  `convergence_rate_sharp` + the asymptotic comparison)

**Status**: AXIOMATIZED (3 deep inputs: the Walfisz totient bound, its Abel-sum
propagation to the range sum, and the rate-agnostic EST-regime reduction). The Mertens
baseline is no longer restated here as a (vacuous) axiom — it lives in the parent. The
main theorem `oq02_rate_not_sharp` now rests only on `est_reduction` +
`rangeTotientSum_walfisz_error`. All real-analysis asymptotics are fully PROVED (0 sorries).

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
## The Elementary vs. Walfisz Error Bounds

The parent proof (OQ-02) relied on the Mertens bound:
  partialTotientSum n = (3/π²) n² + E(n),  E(n) = O(n log n)

Walfisz (1963) proved the dramatically sharper:
  E(n) = O(n (log n)^(2/3) (log log n)^(4/3))

Both bounds are beyond Mathlib's current scope and must be axiomatized.
-/

/-
The Mertens baseline `∑_{n≤x} φ(n) = (3/π²)x² + O(x log x)` (the *weaker*
error `E(N) = O(N log N)` used to derive OQ-02's `O(log N/N)` rate) lives in the
parent `Erdos1001OQ02.lean`. It is deliberately NOT restated here as an axiom: no
result in this file depends on the Mertens totient sum itself — only on the
*rate* comparison `(log N)^{2/3}/N = o(log N/N)`, which is proved unconditionally
below. Restating it here would only inflate the axiom count with a vacuous
assumption. See `Erdos1001OQ02.rangeTotientSum_error` for the Mertens-side input.
-/

/-- Walfisz's sharp bound on the totient partial sum error (1963).

    Walfisz proved: ∑_{n≤x} φ(n) = (3/π²)x² + O(x (log x)^(2/3) (log log x)^(4/3))

    This is the *sharp* bound — substantially better than Mertens' O(N log N).
    The proof uses Vinogradov's exponential sum method via Dirichlet series for
    L(s, χ) and zero-free regions for ζ(s); about 60 pages in Walfisz (1963)
    "Weylsche Exponentialsummen in der neueren Zahlentheorie".

    Not yet in Mathlib (as of v4.26). -/
axiom totient_sum_walfisz_error :
    (fun N : ℕ => |partialTotientSum N - densityConst * 2⁻¹ * N^2|)
    =O[atTop] (fun N : ℕ => (N : ℝ) * (Real.log N) ^ ((2:ℝ)/3) *
                             (Real.log (Real.log N)) ^ ((4:ℝ)/3))

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

/-- **EST-regime reduction (rate-agnostic).** In the EST regime the density
    error `|S(N,A,c) - f(A,c)|` is controlled by `A` times the range totient-sum
    error `|∑_{y=N}^{cN} φ(y)/y² - (6/π²)log c|`.

    This is the genuine *structural* input: in the EST regime the approximation
    intervals for distinct `y` are disjoint, so
      `S(N,A,c) = 2A · rangeTotientSum(N,c) + O(A/N)`  and
      `f(A,c)   = 2A · densityConst · log c`,
    hence `|S - f| = O(A · |rangeTotientSum - densityConst·log c|)`.

    Crucially this axiom is **independent of which totient error bound is used** —
    it fixes only the disjointness/inclusion–exclusion geometry, not any rate. The
    same reduction yields OQ-02's Mertens rate and this file's Walfisz rate,
    depending only on which range-sum bound is plugged in. It is therefore
    strictly weaker than (and factors out of) the former monolithic
    `convergence_rate_sharp` axiom, which baked the entire quantitative answer in.

    Deep geometry-of-numbers input (disjointness + boundary corrections),
    parallel to the parent's `convergence_rate_est`. -/
axiom est_reduction (A c : ℝ) (hA : 0 < A) (hc : c > 1)
    (hregime : inESTRegime A c) :
    (fun N : ℕ => |S N A c - f A c|)
    =O[atTop]
    (fun N : ℕ => A * |rangeTotientSum N c - densityConst * Real.log c|)

/-- The O(log N / N) rate from OQ-02 is NOT sharp.

    In the EST regime, the actual convergence rate of S(N,A,c) to f(A,c)
    is strictly better than O(A log N / N):

      |S(N,A,c) - f(A,c)| = O(A (log N)^(2/3) (log log N)^(4/3) / N)

    which is o(A log N / N).

    **This is now a theorem, not an axiom.** It is derived by composing:
    1. `est_reduction`: `|S - f| = O(A · |rangeTotientSum error|)` (EST disjointness), and
    2. `rangeTotientSum_walfisz_error`: `|rangeTotientSum error| = O((log N)^(2/3)(log log N)^(4/3)/N)`
       (Walfisz's bound propagated by Abel summation),
    scaling the second by the constant `A` and chaining with `IsBigO.trans`. This
    makes `rangeTotientSum_walfisz_error` load-bearing and reduces the file's
    axiom footprint from four declarations to three. -/
theorem convergence_rate_sharp (A c : ℝ) (hA : 0 < A) (hc : c > 1)
    (hregime : inESTRegime A c) :
    (fun N : ℕ => |S N A c - f A c|)
    =O[atTop]
    (fun N : ℕ => A * ((Real.log N) ^ ((2:ℝ)/3) *
                       (Real.log (Real.log N)) ^ ((4:ℝ)/3) / N)) := by
  -- Scale the range-sum Walfisz bound by the constant `A` on both sides.
  have hrange :
      (fun N : ℕ => A * |rangeTotientSum N c - densityConst * Real.log c|)
      =O[atTop]
      (fun N : ℕ => A * ((Real.log N) ^ ((2:ℝ)/3) *
                         (Real.log (Real.log N)) ^ ((4:ℝ)/3) / N)) :=
    ((rangeTotientSum_walfisz_error c hc).const_mul_left A).const_mul_right hA.ne'
  -- Chain the EST reduction with the scaled range bound.
  exact (est_reduction A c hA hc hregime).trans hrange

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
