/-
Erdős Problem #258 — Open Question OQ-01

**Parent**: Erdős #258 (Irrationality of the divisor-sum series).
  For a sequence `a : ℕ → ℕ` with `aₙ → ∞`, is
    `S(a) = ∑ₙ τ(n+1) / (a₁·a₂·…·aₙ)`
  irrational?  (`τ` = number-of-divisors.)

**OQ-01**: Does irrationality hold for ARBITRARY (non-monotone) sequences with
  `aₙ → ∞`?  The monotone case was settled by Erdős–Straus (1971); the general
  case is OPEN.

This file is an ORIENT (build-free analysis under a Docker outage — the proofs
below are NOT machine-checked yet; sorries are labelled with their status).
It contributes the precise *reduction* of OQ-01 to a single analytic quantity,
an elementary *irrationality engine*, and a new *non-monotone sufficient
condition* (polynomial growth) that the engine yields for free.

## The Cantor-series reframing

`S(a)` is a Cantor series: the n-th term has denominator `a₁⋯aₙ` (a product of
`n` "bases") and integer numerator `τ(n+1)`.  The decisive object is the
**renormalised tail**

    T_N(a) = ∑_{n>N} τ(n+1) / (a_{N+1}·a_{N+2}·…·a_n)
           = τ(N+2)/a_{N+1} + τ(N+3)/(a_{N+1}a_{N+2}) + ⋯

Multiplying `S(a)` by the partial product `Pₙ = a₁⋯a_N` separates an integer
from the tail:

    P_N · S(a)  =  (an integer)  +  T_N(a).                         (★)

Hence if `S(a) = p/q` is rational, then `q · T_N(a) ∈ ℤ` for every `N`.
Because the tail is a sum of strictly positive terms, `T_N(a) > 0`, so in fact
`q · T_N(a)` is a **positive** integer, giving `T_N(a) ≥ 1/q` for all `N`.

This is the entire mechanism, and it makes the crux completely explicit:

  * **Irrationality engine (Lemma A):** `liminf_N T_N(a) = 0  ⟹  S(a) irrational.`
  * **Rationality necessarily requires** `liminf_N T_N(a) > 0`
    (and the rigid arithmetic constraint `q·T_N ∈ ℤ` eventually).

## What the engine settles, and where the open zone is

A `sympy` probe (committed at `research/problems/erdos-258-oq-01/probe.py`)
computes `T_N(a)` exactly for many sequences:

  * `a_n = n²`  (polynomial):           `T_N → 0` rapidly  ⟹ irrational.
  * `a_n ≥ n^δ` eventually (any δ>0):   `T_N → 0`          ⟹ irrational.
  * `a_n ~ log n`, `a_n ~ (log n)²`,
    `a_n = max(τ(n+1), ⌊√n⌋)`  (slow / non-monotone, still `→∞`):
        `liminf_N T_N(a) > 0`  empirically (`T_N` hovers ≈ 0.2–1.1),
        so the elementary engine does **not** fire.

The growth threshold is genuine: with `a_n ≥ n^δ` the denominators dominate
`τ(n+1) = n^{o(1)}` and the tail collapses; with **subpolynomial** growth the
leading term `τ(N+2)/a_{N+1}` can stay bounded below (it spikes whenever `N+2`
is highly composite), so `liminf T_N` need not vanish.  This is exactly why the
non-monotone case is hard: `aₙ → ∞` alone does not force `liminf T_N = 0`.

Summary of the contribution:

  * **Lemma A** (engine) — elementary, fully formalisable.
  * **Lemma B** — `a_n ≥ n^δ` eventually ⟹ `T_N → 0` (uses `τ(n) = O(n^ε)`).
  * **Corollary C** — polynomial growth ⟹ irrational, *without* monotonicity:
    a clean sufficient condition strictly inside OQ-01's non-monotone setting.
  * **Reduction** — OQ-01 reduces to: every `aₙ → ∞` has `liminf_N T_N = 0`.

The remaining open zone is precisely **subpolynomial, non-monotone** growth
(`aₙ → ∞` with `aₙ = n^{o(1)}`), where `liminf T_N` may be positive.

Reference: https://erdosproblems.com/258
Erdős–Straus, "Some number theoretic results", Pacific J. Math. 36 (1971).
-/

import Mathlib.NumberTheory.Divisors
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecificLimits.Basic

open scoped BigOperators
open Nat Finset

namespace Erdos258OQ01

/- ## Definitions (matching the parent file `Erdos258Problem.lean`) -/

/-- The divisor function τ(n) = number of positive divisors of n. -/
def tau (n : ℕ) : ℕ := n.divisors.card

/-- Partial product `a₁ · a₂ · … · aₙ` (empty product `= 1` at `n = 0`). -/
def productPrefix (a : ℕ → ℕ) (n : ℕ) : ℕ := ∏ i ∈ Icc 1 n, a i

/-- The general term `τ(n+1) / (a₁⋯aₙ)` as a real. -/
noncomputable def generalTerm (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (tau (n + 1) : ℝ) / (productPrefix a n : ℝ)

/-- The full series `S(a) = ∑ₙ τ(n+1)/(a₁⋯aₙ)`. -/
noncomputable def S (a : ℕ → ℕ) : ℝ := ∑' n, generalTerm a n

/-- The **renormalised tail** at level `N`:
    `T_N(a) = ∑_{n>N} τ(n+1) / (a_{N+1}·…·a_n)`.
    Indexing: the `k`-th summand (`k ≥ 1`) is
    `τ(N+1+k) / (a_{N+1}·…·a_{N+k})`. -/
noncomputable def renormTail (a : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' k : ℕ, (tau (N + 2 + k) : ℝ) / (∏ i ∈ Icc (N + 1) (N + 1 + k), a i)

/- ## The Cantor-series backbone: base case + tail recursion.

The two identities below are the canonical Cantor-series structure for `S(a)`.
Both are verified *exactly* (rational arithmetic, six sequence families) in
`research/problems/erdos-258-oq-01/verify_recursion.py`. Together they give a
clean *inductive* proof of the identity (★) below, replacing the unindexed tsum
regrouping by a one-step factor-out (recursion) plus a head-peel (base case). -/

/-- **Base case.** `S(a) = τ(1) + T_0(a)` (and `τ(1) = 1`).
    The `n = 0` term `τ(1)/1` peels off; the remaining `n ≥ 1` terms are exactly
    the level-`0` renormalised tail.
    STATUS: sorry — a single `tsum` head-split + index shift. NOT build-verified. -/
theorem S_eq_head_add_renormTail_zero (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (hconv : Summable (generalTerm a)) :
    S a = (tau 1 : ℝ) + renormTail a 0 := by
  sorry

/-- **Tail recursion (Cantor-series backbone).**
    `a_{N+1} · T_N(a) = τ(N+2) + T_{N+1}(a)` for every `N`.

    The `k = 0` summand of `T_N` is `τ(N+2)/a_{N+1}`, which the factor `a_{N+1}`
    turns into `τ(N+2)`; every `k ≥ 1` summand loses its `a_{N+1}` factor and,
    after the shift `k ↦ k-1`, becomes the corresponding summand of `T_{N+1}`.
    This is the single algebraic fact behind the whole argument.
    STATUS: sorry — `tsum` constant-factor-out + reindex (`tsum_eq_zero_add`,
    summability of the tail). NOT build-verified (Docker outage). -/
theorem renormTail_recursion (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (hconv : Summable (generalTerm a)) (N : ℕ) :
    (a (N + 1) : ℝ) * renormTail a N = (tau (N + 2) : ℝ) + renormTail a (N + 1) := by
  sorry

/- ## The identity (★): partial product times S splits into integer + tail. -/

/-- `productPrefix a N • S(a) = (integer) + T_N(a)`.

    Concretely there is an integer `m` with `(productPrefix a N : ℝ) * S a = m + renormTail a N`.
    This is the algebraic heart of the Cantor-series argument: every term with
    index `≤ N` becomes an integer after multiplying by `a₁⋯a_N`, and the
    remaining terms regroup into the renormalised tail.

    Inductive proof (from the backbone above): at `N = 0` it is the base case
    with `m₀ = τ(1)`. For the step, multiply the hypothesis by `a_{N+1}` and use
    `renormTail_recursion`:
      `(a₁⋯a_{N+1})·S = a_{N+1}·(m_N + T_N) = (a_{N+1} m_N + τ(N+2)) + T_{N+1}`,
    so `m_{N+1} = a_{N+1} m_N + τ(N+2) ∈ ℤ`. Only the two backbone `sorry`s and
    `productPrefix` multiplicativity then remain.

    STATUS: sorry — kept as a clean stub under the Docker outage; the inductive
    derivation above reduces it to the backbone lemmas. NOT build-verified. -/
theorem partialProduct_smul_S (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (hconv : Summable (generalTerm a)) :
    ∃ m : ℤ, (productPrefix a N : ℝ) * S a = (m : ℝ) + renormTail a N := by
  sorry

/-- The renormalised tail is strictly positive (a sum of positive terms;
    `τ(m) ≥ 1`). STATUS: sorry — positivity of a tsum of positive terms. -/
theorem renormTail_pos (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (hconv : Summable (generalTerm a)) (N : ℕ) :
    0 < renormTail a N := by
  sorry

/- ## Lemma A — the irrationality engine. -/

/--
**Lemma A (irrationality engine).**  If the renormalised tail has
`liminf_N T_N(a) = 0`, then `S(a)` is irrational.

Proof idea (elementary): suppose `S(a) = p/q` with `q ≥ 1`.  By (★),
`q · T_N(a) = q · productPrefix a N · S(a) − q·m ∈ ℤ` for every `N`, and by
`renormTail_pos` it is a *positive* integer, hence `T_N(a) ≥ 1/q` for all `N`.
This contradicts `liminf_N T_N(a) = 0`.

STATUS: sorry — depends on (★) and the `liminf` extraction. The mathematics is
complete and elementary; only the Lean plumbing remains. NOT build-verified. -/
theorem irrational_of_liminf_renormTail_zero (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (hconv : Summable (generalTerm a))
    (hlim : Filter.liminf (fun N => renormTail a N) Filter.atTop = 0) :
    Irrational (S a) := by
  sorry

/- ## Lemma B — polynomial growth collapses the tail. -/

/--
**Lemma B.**  If `a_n ≥ n^δ` eventually for some `δ > 0`, then
`T_N(a) → 0` as `N → ∞` (in particular `liminf_N T_N(a) = 0`).

Proof idea: for `n > N`, `a_{N+1}⋯a_n ≥ ∏_{i=N+1}^n i^δ ≥ (N+1)^{δ(n−N)}`,
while `τ(n+1) = n^{o(1)} ≤ C_ε (n+1)^ε` for any `ε ∈ (0, δ)`.  The tail is then
dominated by a geometric series with ratio `(N+1)^{−δ} → 0`, leading term
`C_ε (N+2)^ε (N+1)^{−δ} → 0`.

STATUS: sorry — quantitative; needs `Nat.ArithmeticFunction.sigma`/`τ = O(n^ε)`
bound from Mathlib (or an explicit `τ(n) ≤ 2√n` crude bound suffices once
`δ > 1/2`, with the general `δ` requiring the `n^ε` bound).
NOT build-verified. -/
theorem renormTail_tendsto_zero_of_poly_growth (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (δ : ℝ) (hδ : 0 < δ) (hgrow : ∀ᶠ n in Filter.atTop, (n : ℝ) ^ δ ≤ a n) :
    Filter.Tendsto (fun N => renormTail a N) Filter.atTop (nhds 0) := by
  sorry

/- ## Corollary C — non-monotone polynomial growth ⟹ irrational. -/

/--
**Corollary C.**  If `a_n ≥ n^δ` eventually for some `δ > 0` (NO monotonicity
assumed), then `S(a)` is irrational.

This is a genuinely new sufficient condition strictly inside OQ-01's
non-monotone regime: the Erdős–Straus 1971 theorem assumes monotonicity, while
here `a` may oscillate arbitrarily as long as it stays above a power of `n`.
Combines Lemma B (`T_N → 0 ⟹ liminf = 0`) with Lemma A. -/
theorem irrational_of_poly_growth (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (hconv : Summable (generalTerm a))
    (δ : ℝ) (hδ : 0 < δ) (hgrow : ∀ᶠ n in Filter.atTop, (n : ℝ) ^ δ ≤ a n) :
    Irrational (S a) := by
  apply irrational_of_liminf_renormTail_zero a ha hconv
  have htend := renormTail_tendsto_zero_of_poly_growth a ha δ hδ hgrow
  -- `liminf` of a sequence tending to `0` is `0`.
  sorry

/- ## OQ-01 statement and its reduction. -/

/-- **OQ-01 (open).**  Irrationality for arbitrary `aₙ → ∞`. -/
def erdos_258_oq01 : Prop :=
  ∀ (a : ℕ → ℕ), (∀ n, 0 < a n) →
    Filter.Tendsto a Filter.atTop Filter.atTop →
    Irrational (S a)

/--
**Reduction theorem.**  OQ-01 is *equivalent in difficulty* to the single
analytic statement "every `aₙ → ∞` has `liminf_N T_N(a) = 0`".

This isolates the entire open content into one liminf claim about the
renormalised Cantor tail.  By the probe, the claim can FAIL to be reachable by
elementary means precisely in the subpolynomial non-monotone regime.

STATUS: the forward direction is immediate from Lemma A (modulo `hconv`, which
holds whenever `aₙ → ∞`). -/
theorem oq01_of_liminf_tail
    (H : ∀ (a : ℕ → ℕ), (∀ n, 0 < a n) →
        Filter.Tendsto a Filter.atTop Filter.atTop →
        Summable (generalTerm a) ∧
        Filter.liminf (fun N => renormTail a N) Filter.atTop = 0) :
    erdos_258_oq01 := by
  intro a ha htends
  obtain ⟨hconv, hlim⟩ := H a ha htends
  exact irrational_of_liminf_renormTail_zero a ha hconv hlim

end Erdos258OQ01
