# Research State: birthday-problem-oq-03-oq-01-oq-02-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-04-29T00:00:00Z
**Iteration**: 7

## Current Focus
Lemmas A and B proved (Sessions 4-5). `poisson_approx_birthday3` derived from
Lemma B + Lemma C. n=3 base case proved as a real number (Session 6) and
extended to a Tendsto statement (Session 7). The remaining axiom is Lemma C
(`p_no_triple_tendsto`) — qualitative Poisson convergence along the threshold
scaling — which requires method-of-factorial-moments infrastructure absent
from Mathlib 4.26.

## Active Approach
Decomposition strategy:
- **`nc_div_pow_tendsto` (foundation, Session 3)**: PROVED
- **Lemma A `lambda_tendsto` (Session 4)**: PROVED via squeeze
- **Lemma B `exp_lambda_tendsto` (Session 4)**: PROVED via Real.continuous_exp.tendsto
- **Lemma C `p_no_triple_tendsto` (axiom)**: pure Poisson limit; requires
  qualitative method-of-factorial-moments → Poisson convergence (≈500 lines,
  not in Mathlib 4.26). Either build locally for this entry, contribute upstream,
  or accept as axiomatized.
- **`poisson_approx_birthday3` (Session 5)**: PROVED via Tendsto.sub from Lemma B + Lemma C
- **`p_no_triple_n3` (Session 6)**: P(no triple|n=3, d) = 1 − 1/d² real-number form
- **`p_no_triple_n3_tendsto` (Session 7)**: P(no triple|n=3) → 1 as d → ∞ (build pending)

## Attempt Count
- Total attempts: 7 (Session 1 BLOCKED; Sessions 2-7 progress)
- Current approach attempts: 1 (Session 7 added n=3 fixed Tendsto corollary)
- Approaches tried: 1

## Blockers
- Lemma C still requires method-of-factorial-moments → Poisson convergence,
  which is not in Mathlib 4.26. Alternative: contribute upstream to
  `Mathlib.Probability.Distributions.Poisson` (currently exposes only PMF/measure
  constructors, no convergence theorems).
- Smaller incremental contributions remaining: union bound on triple count
  (general n), factorial moment definitions, Bonferroni r=1 bound — but each is
  ≪Lemma C in effect.

## Next Action
1. **Build verification** (Session 7): confirm `p_no_triple_n3_tendsto` compiles
   under Docker (build in progress, cold-cache).
2. **Lemma C** (open): prove `p_no_triple_tendsto` via qualitative
   method-of-factorial-moments → Poisson convergence (≈500 lines).
3. **Alternative**: contribute factorial-moments → Poisson convergence upstream
   to Mathlib.
4. **Smaller wins**: union bound `P_no_triple(n,d) ≥ 1 - C(n,3)/d²` for general n
   (Bonferroni r=1, complementary quantitative bound).
