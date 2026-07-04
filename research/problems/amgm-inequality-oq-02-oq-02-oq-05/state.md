# Research State: amgm-inequality-oq-02-oq-02-oq-05

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-04
**Iteration**: 6 (PART V)

## Iteration 6 (PART V — general Rolle crux, closed via Mathlib)
**Retired the long-standing "multi-week" blocker.** The iterated-Rolle crux
"differentiation preserves full real-rootedness counting multiplicity" was
recorded as "not in Mathlib" — but Mathlib's
`Polynomial.card_roots_le_derivative`
(`Analysis/Calculus/LocalExtr/Polynomial.lean`) supplies exactly the hard,
multiplicity-counted half. Four new theorems (20 → 24; docker-build clean, 7743
jobs; 0 sorries, 0 axioms):
- `derivative_roots_card_eq`: `card p.roots = natDegree p ⇒
  card (derivative p).roots = natDegree (derivative p)` — THE CRUX, all `n`. A
  4-line `omega` sandwich of `card_roots_le_derivative`, `card_roots'`,
  `natDegree_derivative_lt`.
- `splits_derivative` / `splits_iterate_derivative`: `Splits`-level and iterated
  forms (all `k` derivatives of `∏(X−xᵢ)` split).
- `exists_isRoot_derivative_Ioo`: the per-gap Rolle atom for the `Polynomial` API.
The real-rootedness half of the classical Newton proof is now general. Remaining:
pure coefficient bookkeeping (identify the `(n−k−1)`-th derivative as the quadratic
in `eₖ₋₁,eₖ,eₖ₊₁`, then feed the Part I discriminant atom).

## Iteration 5 (PART IV — n = 4 via SOS), PR #34576
Discharged **ALL THREE** Newton log-concavity steps at `n = 4` for arbitrary
SIGNED reals, via explicit SOS certificates (docker-build clean, 7743 jobs; 0
sorries, 0 axioms). This reaches the middle (`k = 2`) and top (`k = 3`) steps
that Part III's general `k = 1` QM–AM route does not cover, answering the
entry's "extend the SOS approach to n = 4" open question. Four new theorems
(16 → 20):
- `newton_four_first`:  `8 e₂ ≤ 3 e₁²`   — SOS `∑_{i<j}(xᵢ−xⱼ)²`.
- `newton_four_second`: `9 e₁ e₃ ≤ 4 e₂²` — SOS
  `3∑(xᵢxⱼ−xₖxₗ)² + ½∑((xᵢ−xⱼ)(xₖ−xₗ))²` (three opposite-pair splittings).
- `newton_four_third`:  `8 e₂ e₄ ≤ 3 e₃²` — SOS `∑_{i<j}(xᵢ−xⱼ)²(xₖxₗ)²`, the
  reciprocal-polynomial image of the `k = 1` certificate.
- `newton_four_normalized`: all three in normalized p-form.
Certificates derived + verified symbolically (sympy: exact identities, 0
numerical violations over 30k random signed samples). Method: the general Rolle
crux is NOT needed at fixed arity — each Newton inequality at `n = 4` is a PSD
quartic form whose SOS decomposition `nlinarith` verifies from the listed
squares. Next SOS increment would be `n = 5` (degrees rise; feasibility of
explicit certificates is the open question).

## Iteration 4 (PART III) Focus
Proved the genuinely **arbitrary-`n`** first Newton (= first Maclaurin)
inequality `p₁² ≥ p₀ p₂` for SIGNED reals — no enumeration, no appeal to the
still-open iterated-Rolle crux. Three new theorems in
`Proofs/AmgmInequalityOQ02OQ02OQ05.lean` (docker-build clean, 7743 jobs,
`LEAN_SKIP_CACHE=true`; 0 sorries, 0 axioms — foundational only):

- `sq_sum_eq`: the square-of-sum / elementary-symmetric identity
  `(∑_{i<n} xᵢ)² = ∑_{i<n} xᵢ² + 2 ∑_{j<n} ∑_{i<j} xᵢ xⱼ`, i.e. `e₁² = p₂ + 2 e₂`,
  proved by a clean induction on `n` (no triangular reindexing — the `succ` step
  is `sum_range_succ ×3`, `Finset.sum_mul`, then `linear_combination ih`).
- `sq_sum_le_nat_mul_sum_sq`: QM–AM `(∑ xᵢ)² ≤ n · ∑ xᵢ²`, specializing Mathlib's
  Chebyshev lemma `sq_sum_le_card_mul_sum_sq` to `range n` via `card_range`.
- `newton_first_general`: `2 n · e₂ ≤ (n − 1) · e₁²` for all `n` and all signed
  reals — the normalized `p₁² ≥ p₀ p₂` after clearing denominators. Proof:
  substitute `p₂ = e₁² − 2 e₂` into `e₁² ≤ n p₂`.

This closes the `k = 1` (first) Newton inequality for EVERY arity at once,
subsuming the earlier per-arity `n = 2` (`newton_two_vars`) and `n = 3`
(`newton_three_first`) first steps. The theorem needed only *real* inputs (QM–AM
is sign-agnostic), matching the real-rootedness route's signed-input advantage.

## Active Approach
Two complementary engines now coexist in the file:
1. real-rootedness / discriminant (Parts I–II): `n = 2`, `n = 3` per-arity, both
   log-concavity steps, via SOS discriminant certificates;
2. QM–AM / square-of-sum identity (Part III): the `k = 1` step for ALL `n`.

The GENERAL higher steps (`k ≥ 2`, arbitrary `n`) still need the packaged
iterated-Rolle lemma "differentiation preserves full real-rootedness counting
multiplicity".

## Attempt Count
- Total attempts: 5
- Current approach attempts: 1 (QM–AM route)
- Approaches tried: real-rooted/discriminant atom + n=2 (I); n=3 both steps via
  SOS (II); general-n first step via QM–AM + square-of-sum identity (III)

## Blockers
- **RESOLVED (Part V)**: the "differentiation preserves full real-rootedness
  counting multiplicity" crux — previously flagged multi-week / "not in Mathlib"
  — is now `derivative_roots_card_eq`, assembled from Mathlib's
  `card_roots_le_derivative`. No longer a blocker.
- **REMAINING (algebra, not analysis)**: the coefficient reduction turning the
  crux into the general `k ≥ 2` Newton *inequality* — identify the `(n−k−1)`-th
  derivative of the reversed splitting polynomial as `a eₖ₋₁X² − b eₖX + c eₖ₊₁`
  (Vieta / `Polynomial.coeff` bookkeeping), then apply the Part I discriminant
  atom. This is `coeff`-level algebra, medium difficulty, no analysis blocker.

## Next Action
1. Prove the coefficient-extraction lemma: `coeff` of the `m`-fold derivative of
   `∏(X−xᵢ)` in terms of `esymm`, specialised to isolate three consecutive
   `eₖ₋₁,eₖ,eₖ₊₁` (use `Polynomial.coeff_iterate_derivative` /
   `Mathlib.RingTheory.Polynomial.Vieta`).
2. Feed the resulting real-rooted quadratic (real-rooted by
   `derivative_roots_card_eq`) into `discrim_nonneg_of_roots_nonempty` to close
   general `k ≥ 2` Newton.
