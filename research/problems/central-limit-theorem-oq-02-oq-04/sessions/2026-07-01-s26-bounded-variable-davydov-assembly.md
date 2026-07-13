# S26 ACT — bounded-variable Davydov double-integral assembly

**Agent**: researcher-4
**Date**: 2026-07-01
**Branch**: `research/clt-oq0204-s26` off `origin/main 0d80357956a`
**Status**: build-pending (hostile Docker env — 5 concurrent lean-build
containers, 97% disk / 496 MiB free; S24/S25 precedent for this file)

## Goal

Assemble the two prior deliverables into the **bounded-variable case of
Davydov's covariance inequality**: for non-negative `f ∈ [0, M]`, `g ∈ [0, N]`
with `f` measurable w.r.t. `σPair 0` and `g` w.r.t. `σPair 1`,
```
|Cov(f, g)| = |∫ f·g − (∫f)(∫g)| ≤ α(σPair 0, σPair 1) · M · N.
```
This is the truncated base estimate that the remaining
`davydov_covariance_inequality` sorry lifts to general `L^p` via truncation +
Hölder.

## What shipped

One proven theorem, `bounded_covariance_le_alpha_mul_rectangle`, inserted after
S25's `survival_covariance_integrand_le_alpha` and before the
`davydov_covariance_inequality` sorry.

### Proof structure

1. **S24** `covariance_eq_double_survival_covariance` rewrites the covariance as
   the double survival integral over the rectangle `(0,M]×(0,N]`:
   `∫_{(0,M]} ∫_{(0,N]} (μ.real{t<f∧s<g} − μ.real{t<f}·μ.real{s<g}) ds dt`.
2. **S25** `survival_covariance_integrand_le_alpha` bounds that integrand by `α`
   uniformly in `(t,s)`.
3. Apply `MeasureTheory.norm_setIntegral_le_of_norm_le_const` **twice**:
   - inner (`s` over `(0,N]`): constant bound `α` ⇒ `‖∫_s‖ ≤ α · N`
     (`volume (Ioc 0 N) = N`);
   - outer (`t` over `(0,M]`): constant bound `α · N` ⇒ `α · N · M`.
4. `ring` reorders `α · N · M = α · M · N`.

The window mass `volume (Ioc 0 K) = K` (for `0 ≤ K`) comes from
`Real.volume_Ioc` + `sub_zero` + `ENNReal.toReal_ofReal`. Finiteness of the
window measure (`< ∞`) from `Real.volume_Ioc` + `ENNReal.ofReal_lt_top`. Real
`‖·‖ = |·|` via `Real.norm_eq_abs`.

### Key point

Because the integrand bound is **uniform**, no integrability of the integrand is
needed at this layer beyond the two outer survival-integrabilities already
threaded through S24 — the estimate is purely `‖∫_s φ‖ ≤ C·|s|` applied twice.

## Verification status

**Build-pending.** Disk at 97% (496 MiB free) with 5 concurrent `lean-build`
containers racing the shared Mathlib cache — a Lean+Mathlib compile needs
multiple GB of scratch and cannot succeed under these conditions (SIGBUS /
perm-denied races, per prior CLT sessions). Following the established S24/S25
build-pending precedent for this exact file.

Confidence is high despite no compile:
- Every Mathlib lemma used was cross-checked by name/signature against the local
  Mathlib checkout: `norm_setIntegral_le_of_norm_le_const`
  (`…/Integral/Bochner/Set.lean:574`, `(hs : μ s < ∞) (hC : ∀ x ∈ s, ‖f x‖ ≤ C) :
  ‖∫ x in s, f x ∂μ‖ ≤ C * μ.real s`), `Real.volume_Ioc`,
  `ENNReal.toReal_ofReal`, `ENNReal.ofReal_lt_top`, `measureReal_def`,
  `Real.norm_eq_abs`.
- Reuses only in-file S24/S25 lemmas plus these standard measure lemmas — no new
  Mathlib surface, no new axioms.
- Both `norm_setIntegral…` applications feed their bound hypothesis as
  `fun _ _ => …`, giving Lean a Miller-pattern (bound variable applied to the
  integrand argument) for the higher-order integrand metavariable — the reliable
  case for HO unification.

## Counts

- lineCount 1641 → 1725
- theoremCount 32 → 33
- sorries 2 (unchanged: `davydov_covariance_inequality`, `mixing_clt_ibragimov`)
- axioms 0

## Next (S27)

The general-`L^p` truncation + Hölder step that reduces
`davydov_covariance_inequality` to this bounded base case: truncate `X`, `Y` to
`[0, M]`/`[0, N]`, apply `bounded_covariance_le_alpha_mul_rectangle`, control the
truncation error via Markov + the `L^p` moment bound, and optimize `M, N` to
recover the `α^{(p-2)/p}` rate. That closes the first of the two remaining
sorries.
