# Research State: birthday-problem-oq-03-oq-01-oq-02-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-04-29T00:00:00Z
**Iteration**: 3

## Current Focus
Lemma A's foundation is in source (`nc_div_pow_tendsto`); next is the
remainder of Lemma A (cubing + falling-factorial correction) and Lemma B.

## Active Approach
Decomposition strategy:
- **`nc_div_pow_tendsto` (foundation, Session 3)**: `n_c(d) / d^(2/3) → c` —
  direct corollary of `tendsto_nat_floor_mul_div_atTop` ∘ `tendsto_rpow_atTop`.
  In source as of 2026-04-29 (build verification deferred — Docker
  unresponsive during session).
- Lemma A `lambda_tendsto`: `λ(d) := C(⌊c·d^(2/3)⌋, 3)/d² → c³/6` — pending,
  builds on `nc_div_pow_tendsto` via `.pow 3` + falling-factorial correction.
- Lemma B `exp_lambda_tendsto`: `exp(−λ(d)) → exp(−c³/6)` — pending one-liner
  once Lemma A is in.
- Lemma C `p_no_triple_tendsto`: `P_no_triple(n d, d) → exp(−c³/6)` (Poisson
  convergence — only sublemma requiring new Mathlib infrastructure).

## Attempt Count
- Total attempts: 2 (Session 1 BLOCKED; Session 2 ORIENT decomposition; Session 3 ACT-partial)
- Current approach attempts: 1 (Session 3 added Lemma A foundation)
- Approaches tried: 1

## Blockers
- Docker build was unresponsive during Session 3 — verification of the new
  lemma is deferred to a later session. The proof body is two lines composing
  Mathlib lemmas whose signatures were verified by direct file read.
- Lemma C still requires method-of-factorial-moments → Poisson convergence,
  which is not in Mathlib but is substantially smaller than full Chen-Stein.

## Next Action
1. **Verify** `nc_div_pow_tendsto` builds cleanly (Docker)
2. **Add Lemma A** proper (`lambda_tendsto`) using `nc_div_pow_tendsto.pow 3` +
   the `(C(n,3) : ℝ) - n³/6` correction → 0 lemma
3. **Add Lemma B** as a one-liner via `Real.continuous_exp.tendsto`
4. **Restate the axiom** as the strictly weaker Lemma C alone, isolating the
   genuine Mathlib gap to one statement
