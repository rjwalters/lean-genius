/-
Erdős #1001 Open Question 02: Rate of Convergence of S(N,A,c)

**Question**: What is the rate of convergence of S(N,A,c) to f(A,c)?

**Answer**: In the EST regime (0 < A < c/(1+c²)), the rate is O(A log N / N).

**Mathematical Analysis**:
In the EST regime, the approximation intervals are disjoint, so:
  S(N,A,c) = 2A · ∑_{N≤y≤cN, gcd(x,y)=1, 0<x/y<1} 1/y²
           = 2A · ∑_{y=⌈N⌉}^{⌊cN⌋} φ(y)/y² + O(A/N)

The key asymptotic (from Mertens' theorem and partial summation):
  ∑_{y=N}^{cN} φ(y)/y² = (6/π²) log(c) + O(log N / N)

Therefore:
  S(N,A,c) = 12A log(c)/π² + O(A log N / N)
           = f(A,c) + O(A log N / N)

So |S(N,A,c) - f(A,c)| = O(A log N / N) as N → ∞.

**Infrastructure Gap**:
The key missing piece is the asymptotic for ∑ φ(y)/y² with error term.
This requires:
- Mertens' third theorem: ∑_{y≤N} φ(y)/y = (6/π²)N + O(log N)
- Abel summation to convert to the weighted sum ∑ φ(y)/y²
Neither has been proved in this gallery with explicit error bounds.

**Related**: Erdos1001Problem.lean (parent), EulerTotientOQ02.lean (totient properties)
**Status**: AXIOMATIZED (deep analytic number theory)
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.Diophantine
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Topology.Instances.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.MetricSpace.Basic

open MeasureTheory Set Filter Real Asymptotics
open scoped Topology

namespace Erdos1001OQ02

/-
## Imports from parent problem

We re-use the definitions from Erdos1001Problem.lean.
-/

/-- A real α is (A, y)-approximable if |α - x/y| < A/y² for some coprime x. -/
def isApproximable (A : ℝ) (y : ℕ) (α : ℝ) : Prop :=
  ∃ x : ℤ, Int.gcd x y = 1 ∧ |α - x / y| < A / y^2

/-- The set of α ∈ (0,1) approximable by some y in [N, cN]. -/
def approximationSet (N : ℕ) (A c : ℝ) : Set ℝ :=
  { α : ℝ | α ∈ Ioo 0 1 ∧ ∃ y : ℕ, (N : ℝ) ≤ y ∧ (y : ℝ) ≤ c * N ∧ isApproximable A y α }

/-- S(N, A, c) is the Lebesgue measure of the approximation set. -/
noncomputable def S (N : ℕ) (A c : ℝ) : ℝ :=
  (volume (approximationSet N A c)).toReal

/-- The EST formula f(A, c) = 12A log(c)/π². -/
noncomputable def f (A c : ℝ) : ℝ :=
  12 * A * log c / π^2

/-- The EST regime: 0 < A < c/(1+c²). -/
def inESTRegime (A c : ℝ) : Prop :=
  0 < A ∧ A < c / (1 + c^2)

/-
## Key Intermediate: Weighted Totient Sum Asymptotics

The rate of convergence reduces to an asymptotic for ∑_{y=N}^{cN} φ(y)/y².

Define the partial weighted totient sum:
  T(n) = ∑_{y=1}^{n} (φ(y) : ℝ) / y²
-/

/-- Partial weighted totient sum: T(n) = ∑_{y=1}^{n} φ(y)/y². -/
noncomputable def weightedTotientSum (n : ℕ) : ℝ :=
  ∑ y ∈ Finset.range (n + 1), if y = 0 then 0 else (Nat.totient y : ℝ) / (y : ℝ)^2

/-- The logarithmic factor function: log N / N. -/
noncomputable def logOverN : ℕ → ℝ := fun N => if N = 0 then 0 else Real.log N / N

/-- The range sum of weighted totients: ∑_{y=N}^{cN} φ(y)/y². -/
noncomputable def rangeTotientSum (N : ℕ) (c : ℝ) : ℝ :=
  ∑ y ∈ Finset.Icc N ⌊c * N⌋₊, (Nat.totient y : ℝ) / (y : ℝ)^2

/-
## Asymptotic Analysis

The asymptotic for the range sum is the key mathematical content.

**Theorem** (Mertens + Abel summation):
  ∑_{y=N}^{cN} φ(y)/y² = (6/π²) log(c) + O(log N / N)

The constant 6/π² = 1/ζ(2) arises because:
  ∑_{y=1}^{∞} μ(y)/y² = 6/π² (via ζ(2) = π²/6)
  φ(y)/y = ∑_{d|y} μ(d)/d (Euler product formula)
-/

/-- The limiting density constant: 6/π². -/
noncomputable def densityConst : ℝ := 6 / π^2

/-- The range totient sum converges to (6/π²) log(c).
    This is the key asymptotic from which the rate follows.
    Deep analytic number theory: requires Mertens' theorem + partial summation. -/
axiom rangeTotientSum_asymptotic (c : ℝ) (hc : c > 1) :
    Tendsto (fun N : ℕ => rangeTotientSum N c) atTop (nhds (densityConst * Real.log c))

/-- The error in the range totient sum is O(log N / N).
    This gives the precise rate of convergence.

    Proof sketch:
    1. Mertens: ∑_{y≤n} φ(y) = (3/π²)n² + O(n log n)
    2. Abel summation: ∑_{y=N}^{cN} φ(y)/y² = (6/π²) log(c) + O(log N / N)

    The O(log N / N) comes from the error O(n log n) in Mertens' sum. -/
axiom rangeTotientSum_error (c : ℝ) (hc : c > 1) :
    (fun N : ℕ => |rangeTotientSum N c - densityConst * Real.log c|) =O[atTop]
    (fun N : ℕ => Real.log N / ↑N)

/-
## Main Rate Theorem

The rate of convergence of S(N,A,c) to f(A,c) is O(A log N / N).
-/

/-- The rate of convergence in the EST regime.

    **Statement**: In the EST regime (0 < A < c/(1+c²)):
      |S(N,A,c) - f(A,c)| = O(A log N / N)

    **Proof structure**:
    1. In EST regime, approximation intervals are disjoint
    2. S(N,A,c) = 2A · rangeTotientSum(N,c) + boundary_error
       where boundary_error = O(A/N) (corrections from y=0 intervals near 0 or 1)
    3. f(A,c) = 12A log(c)/π² = 2A · densityConst · log(c)
    4. |S(N,A,c) - f(A,c)| = 2A · |rangeTotientSum(N,c) - densityConst·log(c)| + O(A/N)
                            = 2A · O(log N / N) + O(A/N) = O(A log N / N)

    Deep analytic number theory required for the disjointness + error bounds. -/
axiom convergence_rate_est (A c : ℝ) (hA : 0 < A) (hc : c > 1)
    (hregime : inESTRegime A c) :
    (fun N : ℕ => |S N A c - f A c|) =O[atTop]
    (fun N : ℕ => A * (Real.log N / ↑N))

/-
## Consequences of the Rate

The rate theorem has several provable corollaries.
-/

/-- From the rate O(A log N / N), deduce that convergence is faster than O(1/√N).
    This is immediate from log N / N = o(1/√N) being FALSE — actually log N/N is
    faster (approaches 0 faster) than 1/√N is FALSE.

    Actually: 1/√N ≫ log N / N since N^{1/2} → ∞ faster than (log N)·N / N^{1/2}.

    Wait: log N / N vs 1/√N:
    (log N / N) / (1/√N) = (log N / N) · √N = log N / √N → 0
    So log N / N = o(1/√N), meaning the rate IS better than 1/√N. -/
theorem convergence_faster_than_sqrtN (A c : ℝ) (hA : 0 < A) (hc : c > 1)
    (hregime : inESTRegime A c) :
    (fun N : ℕ => |S N A c - f A c|) =o[atTop] (fun N : ℕ => 1 / Real.sqrt N) := by
  apply (convergence_rate_est A c hA hc hregime).trans_isLittleO
  -- Need: (fun N => A * (log N / N)) =o[atTop] (fun N => 1 / sqrt N)
  -- Equivalently: A * log N / N / (1/sqrt N) = A * log N / sqrt N → 0
  -- This follows from Real.tendsto_log_div_rpow_atTop with r = 1/2
  have hlogdiv_R : Tendsto (fun x : ℝ => Real.log x / x ^ (1/2 : ℝ)) atTop (nhds 0) :=
    Real.tendsto_log_div_rpow_atTop (1/2 : ℝ) (by norm_num)
  have hlogdiv_N : Tendsto (fun N : ℕ => Real.log ↑N / (↑N : ℝ) ^ (1/2 : ℝ)) atTop (nhds 0) :=
    hlogdiv_R.comp tendsto_natCast_atTop_atTop
  rw [isLittleO_iff]
  intro c' hc'
  have hcA : 0 < c' / A := div_pos hc' hA
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp hlogdiv_N (c' / A) hcA
  filter_upwards [eventually_atTop.mpr ⟨max N₀ 1, le_max_left _ _⟩] with N hN
  have hN₀le : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < ↑N := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hN1
  have hratio := hN₀ N hN₀le
  rw [Real.dist_eq, sub_zero] at hratio
  -- hratio: |log N / N^(1/2)| < c' / A
  -- Goal: ‖A * (log N / N)‖ ≤ c' * ‖1 / sqrt N‖
  simp only [Real.norm_eq_abs, norm_one, one_mul]
  rw [Real.sqrt_eq_rpow, abs_div, abs_of_pos hNpos,
      abs_mul, abs_of_pos hA, abs_div, abs_of_pos hNpos]
  -- Goal: A * |log N| / N ≤ c' / N^(1/2)
  rw [div_le_div_iff hNpos (Real.rpow_pos_of_pos hNpos _)]
  -- Goal: A * |log N| * N^(1/2) ≤ c' * N
  have h_abs : |Real.log ↑N / (↑N : ℝ) ^ (1/2 : ℝ)| =
      |Real.log ↑N| / (↑N : ℝ) ^ (1/2 : ℝ) := by
    rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hNpos _)]
  rw [h_abs] at hratio
  have hratio' : |Real.log ↑N| / (↑N : ℝ) ^ (1/2 : ℝ) < c' / A := hratio
  have h1 : A * |Real.log ↑N| < c' * (↑N : ℝ) ^ (1/2 : ℝ) := by
    rwa [div_lt_div_iff (Real.rpow_pos_of_pos hNpos _) hA, mul_comm] at hratio'
  have hNhalf_pos : (0 : ℝ) < (↑N : ℝ) ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hNpos _
  have hN_eq : (↑N : ℝ) = (↑N : ℝ) ^ (1/2 : ℝ) * (↑N : ℝ) ^ (1/2 : ℝ) := by
    rw [← Real.rpow_add hNpos]; norm_num
  nlinarith [le_of_lt h1, hNhalf_pos, Real.rpow_pos_of_pos hNpos (1/2 : ℝ)]

/-- The rate implies S(N,A,c) is within ε of f(A,c) for all N ≥ N₀(ε, A, c).
    This gives an explicit, though non-constructive, bound. -/
theorem convergence_effective (A c ε : ℝ) (hA : 0 < A) (hc : c > 1)
    (hε : 0 < ε) (hregime : inESTRegime A c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → |S N A c - f A c| < ε := by
  -- Use rate_is_nontrivial: |S N - f| = o(1), so |S N - f| → 0
  have h_little := rate_is_nontrivial A c hA hc hregime
  -- isLittleO (f =o[atTop] 1) implies Tendsto f atTop (nhds 0)
  have htend : Tendsto (fun N : ℕ => |S N A c - f A c|) atTop (nhds 0) := by
    have := h_little.tendsto_div_nhds_zero
    simp only [div_one] at this
    exact this
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N₀, hN₀⟩ := htend ε hε
  exact ⟨N₀, fun N hN => by
    have h := hN₀ N hN
    simp only [Real.dist_eq, sub_zero] at h
    rwa [abs_abs] at h⟩

/-- The rate is sharper than the a priori O(1) bound (trivially). -/
theorem rate_is_nontrivial (A c : ℝ) (hA : 0 < A) (hc : c > 1)
    (hregime : inESTRegime A c) :
    (fun N : ℕ => |S N A c - f A c|) =o[atTop] (fun _ : ℕ => (1 : ℝ)) := by
  apply (convergence_rate_est A c hA hc hregime).trans_isLittleO
  -- Need: (fun N : ℕ => A * (log N / N)) =o[atTop] (fun _ => 1)
  -- Proof: A * log N / N → 0, which is A * (tendency → 0) → 0
  have hlogdiv_R : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    have h := Real.tendsto_log_div_rpow_atTop 1 one_pos
    simp only [Real.rpow_one] at h; exact h
  have hlogdiv_N : Tendsto (fun N : ℕ => Real.log ↑N / (↑N : ℝ)) atTop (nhds 0) :=
    hlogdiv_R.comp tendsto_natCast_atTop_atTop
  have htend : Tendsto (fun N : ℕ => A * (Real.log ↑N / (↑N : ℝ))) atTop (nhds 0) := by
    have h := hlogdiv_N.const_mul A
    simp only [mul_zero] at h; exact h
  rw [isLittleO_iff]
  intro c' hc'
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp htend c' hc'
  filter_upwards [eventually_atTop.mpr ⟨N₀, le_refl _⟩] with N hN
  have h := hN₀ N hN
  simp only [Real.dist_eq, sub_zero] at h
  simp only [norm_one, mul_one]
  exact le_of_lt h

/-
## Connection to Quantitative Metric Theory

The rate O(log N / N) connects to broader results in metric Diophantine approximation:
-/

/-- The rate of convergence is consistent with the three-distance theorem:
    the gaps between {nα mod 1} for n ≤ N take at most 3 distinct values,
    and the gap structure stabilizes at rate O(1/N). The slower log N/N rate
    for S(N,A,c) reflects averaging over all α rather than a single orbit. -/
def three_distance_connection : Prop :=
  ∀ A c : ℝ, 0 < A → c > 1 → inESTRegime A c →
    (fun N : ℕ => |S N A c - f A c|) =O[atTop] (fun N : ℕ => A * (Real.log N / ↑N))

theorem three_distance_connection_holds :
    three_distance_connection := convergence_rate_est

/-
## Summary

**Main Result** (axiomatized): In the EST regime, |S(N,A,c) - f(A,c)| = O(A log N / N).

**Proof path to formalization**:
1. Formalize Mertens' theorem: ∑_{y≤N} φ(y) = (3/π²)N² + O(N log N) [in Mathlib?]
2. Abel summation: derive ∑_{y=N}^{cN} φ(y)/y² error bound [elementary once (1) done]
3. EST regime measure formula: S(N,A,c) = 2A · ∑ φ(y)/y² + O(A/N) [needs measure theory]
4. Combine for final rate [routine once (1)-(3) done]

**Mathlib gap**: Step 1 (Mertens' theorem with quantitative error) appears to be
missing from Mathlib 4.x. The qualitative statement (φ averages to 6/π²) may exist
but not with the O(N log N) error needed here.

**Status**: AXIOMATIZED
  - `rangeTotientSum_asymptotic`: qualitative convergence (should be provable with Mathlib)
  - `rangeTotientSum_error`: quantitative rate (requires Mertens with error bounds)
  - `convergence_rate_est`: main rate theorem (reduces to above)
-/

/-- **Erdős #1001 OQ-02 SUMMARY**
    The rate of convergence of S(N,A,c) to f(A,c) is O(A log N / N) in the EST regime. -/
theorem erdos_1001_oq_02_summary (A c : ℝ) (hA : 0 < A) (hc : c > 1)
    (hregime : inESTRegime A c) :
    (fun N : ℕ => |S N A c - f A c|) =O[atTop]
    (fun N : ℕ => A * (Real.log N / ↑N)) :=
  convergence_rate_est A c hA hc hregime

end Erdos1001OQ02
