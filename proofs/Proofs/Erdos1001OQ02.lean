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

    Key fact: log N / N = o(1/√N), since
      (log N / N) / (1/√N) = log N · √N / N = log N / √N → 0
    This follows from Real.tendsto_log_div_rpow_atTop with p = 1/2. -/
theorem convergence_faster_than_sqrtN (A c : ℝ) (hA : 0 < A) (hc : c > 1)
    (hregime : inESTRegime A c) :
    (fun N : ℕ => |S N A c - f A c|) =o[atTop] (fun N : ℕ => 1 / Real.sqrt N) := by
  apply (convergence_rate_est A c hA hc hregime).trans_isLittleO
  -- Need: A * (log N / N) = o(1/√N), proved via isLittleO_iff with explicit norm bound
  rw [isLittleO_iff]
  intro c' hc'
  -- log x / x^(1/2) → 0, so A * log N / √N → 0 on ℕ
  have hA_log_sqrt : Tendsto (fun n : ℕ => A * (Real.log ↑n / Real.sqrt ↑n)) atTop (nhds 0) := by
    have hlog12 : Tendsto (fun x : ℝ => Real.log x / x ^ ((1:ℝ)/2)) atTop (nhds 0) :=
      Real.tendsto_log_div_rpow_atTop (1/2) (by norm_num)
    have h : Tendsto (fun n : ℕ => A * (Real.log ↑n / (↑n : ℝ) ^ ((1:ℝ)/2))) atTop (nhds 0) := by
      have := (hlog12.comp tendsto_natCast_atTop_atTop).const_mul A
      simpa [mul_zero] using this
    exact h.congr' (Filter.Eventually.of_forall fun n => by rw [← Real.sqrt_eq_rpow])
  -- Eventually |A * log N / √N| < c', and A * |log N| / N ≤ |A * log N / √N| / √N ≤ c' / √N
  filter_upwards [hA_log_sqrt.eventually (Metric.ball_mem_nhds 0 hc'),
                  eventually_gt_atTop 0] with N hN hNpos
  have hNr : (0 : ℝ) < ↑N := Nat.cast_pos.mpr hNpos
  have hsqrt_pos : 0 < Real.sqrt ↑N := Real.sqrt_pos.mpr hNr
  have hsq : Real.sqrt ↑N * Real.sqrt ↑N = ↑N := Real.mul_self_sqrt (le_of_lt hNr)
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero, Real.norm_eq_abs] at hN
  -- hN : |A * (log N / sqrt N)| < c'
  -- Derive: A * |log N| / sqrt N < c'
  have hN_abs : A * |Real.log ↑N| / Real.sqrt ↑N < c' := by
    rwa [abs_mul, abs_div, abs_of_pos hA, abs_of_pos hsqrt_pos] at hN
  -- Multiply out: A * |log N| < c' * sqrt N
  -- Then: A * |log N| * sqrt N < c' * (sqrt N)² = c' * N
  have hkey : A * |Real.log ↑N| * Real.sqrt ↑N < c' * (Real.sqrt ↑N * Real.sqrt ↑N) := by
    have hmul : A * |Real.log ↑N| < c' * Real.sqrt ↑N := by
      rwa [div_lt_iff hsqrt_pos] at hN_abs
    calc A * |Real.log ↑N| * Real.sqrt ↑N
        < c' * Real.sqrt ↑N * Real.sqrt ↑N := mul_lt_mul_of_pos_right hmul hsqrt_pos
      _ = c' * (Real.sqrt ↑N * Real.sqrt ↑N) := by ring
  -- Rewrite goal norms explicitly then use div_le_div_iff
  have h1 : ‖A * (Real.log ↑N / ↑N)‖ = A * |Real.log ↑N| / ↑N := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hA, abs_div, abs_of_pos hNr]
  have h2 : c' * ‖1 / Real.sqrt ↑N‖ = c' / Real.sqrt ↑N := by
    rw [Real.norm_eq_abs, abs_div, abs_one, abs_of_pos hsqrt_pos]; ring
  -- A * |log N| / N ≤ c' / sqrt N ↔ A * |log N| * sqrt N ≤ c' * N = c' * (sqrt N)²
  rw [h1, h2, div_le_div_iff hNr hsqrt_pos, ← hsq]
  linarith [hkey]

/-- The rate is sharper than the a priori O(1) bound (trivially).

    Proof: A * log N / N → 0 from Real.tendsto_log_div_rpow_atTop (p=1). -/
theorem rate_is_nontrivial (A c : ℝ) (hA : 0 < A) (hc : c > 1)
    (hregime : inESTRegime A c) :
    (fun N : ℕ => |S N A c - f A c|) =o[atTop] (fun _ : ℕ => (1 : ℝ)) := by
  apply (convergence_rate_est A c hA hc hregime).trans_isLittleO
  -- A * (log N / N) = o(1): use Tendsto characterization
  -- isLittleO_of_tendsto: if f N / g N → 0 then f = o(g)
  apply isLittleO_of_tendsto (fun _ h => by norm_num at h)
  -- Goal: Tendsto (fun N => A * (log N / N) / 1) atTop (nhds 0)
  simp only [div_one]
  -- log x / x → 0 on ℝ (from tendsto_log_div_rpow_atTop with p = 1)
  have hlogdiv : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    have h := Real.tendsto_log_div_rpow_atTop 1 one_pos
    simpa [Real.rpow_one] using h
  -- Pull back to ℕ via Nat.cast coercion
  have hlogdiv_nat : Tendsto (fun n : ℕ => Real.log ↑n / (↑n : ℝ)) atTop (nhds 0) :=
    hlogdiv.comp tendsto_natCast_atTop_atTop
  -- A * (log N / N) → A * 0 = 0
  have h := hlogdiv_nat.const_mul A
  simpa [mul_zero] using h

/-- The rate implies S(N,A,c) is within ε of f(A,c) for all N ≥ N₀(ε, A, c).
    This gives an explicit, though non-constructive, bound.

    Proof: From rate_is_nontrivial (|S(N)-f| = o(1)):
    for all ε > 0, eventually |S(N) - f(A,c)| ≤ ε/2 < ε. -/
theorem convergence_effective (A c ε : ℝ) (hA : 0 < A) (hc : c > 1)
    (hε : 0 < ε) (hregime : inESTRegime A c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → |S N A c - f A c| < ε := by
  -- From rate_is_nontrivial: |S N - f| = o(1)
  have ho := rate_is_nontrivial A c hA hc hregime
  rw [isLittleO_iff] at ho
  have h_ev := ho (ε/2) (by linarith)
  simp only [norm_one, mul_one] at h_ev
  rw [Filter.eventually_atTop] at h_ev
  obtain ⟨N₀, hN₀⟩ := h_ev
  exact ⟨N₀, fun N hN => by
    have hle := hN₀ N hN
    simp only [Real.norm_eq_abs, abs_abs] at hle
    linarith⟩

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

**Mathlib gap (verified 2026-04-27 against Mathlib v4.26.0)**: Step 1 (Mertens'
theorem with quantitative error) is still missing. A grep of Mathlib for any
asymptotic of `∑_{y≤N} Nat.totient y` returns no results — only the divisor
identity `Nat.sum_totient : n.divisors.sum φ = n` exists.

**Concrete Mathlib API needed to unblock**:
1. `Nat.totient_partial_sum_asymp`:
     `(fun N => ∑ y ∈ Finset.range (N+1), (Nat.totient y : ℝ)) - (3/π^2) * N^2`
       =O[atTop] (fun N => N * Real.log N)
2. `Nat.totient_div_sq_partial_sum_asymp` (derivable from (1) via `AbelSummation`):
     `(fun N => ∑ y ∈ Finset.range (N+1), (Nat.totient y : ℝ) / y^2) -
       (6/π^2) * Real.log N` =O[atTop] (fun N => Real.log N / N)

Mathlib v4.26 has `Mathlib.NumberTheory.AbelSummation` (378 lines, ~13 theorems
including `sum_mul_eq_sub_sub_integral_mul`), so step (2) is mechanical once (1)
exists. The blocker is purely (1): the average order of φ via Möbius inversion
ζ(s-1)/ζ(s) at s=2 has not been formalized in Mathlib.

**Status**: AXIOMATIZED — BLOCKED on Mathlib gap
  - `rangeTotientSum_asymptotic`: qualitative convergence (REDUCES to (1))
  - `rangeTotientSum_error`: quantitative rate (REDUCES to (1) via AbelSummation)
  - `convergence_rate_est`: main rate theorem (REDUCES to above)

All three axioms above collapse to the SAME Mathlib gap: the totient partial-sum
asymptotic with `O(N log N)` error. There is no incremental progress available
on this file without first contributing that asymptotic to Mathlib (estimated
~500 lines using Möbius-inversion proof, see Apostol §3.7 or Tenenbaum I.3.7).
-/

/-- **Erdős #1001 OQ-02 SUMMARY**
    The rate of convergence of S(N,A,c) to f(A,c) is O(A log N / N) in the EST regime. -/
theorem erdos_1001_oq_02_summary (A c : ℝ) (hA : 0 < A) (hc : c > 1)
    (hregime : inESTRegime A c) :
    (fun N : ℕ => |S N A c - f A c|) =O[atTop]
    (fun N : ℕ => A * (Real.log N / ↑N)) :=
  convergence_rate_est A c hA hc hregime

end Erdos1001OQ02
