# Problem Selection Report

**Date**: 2026-04-05
**Mode**: SELECT
**Pool Status**: 17 available, 509 in-progress, 1236 completed

## Selected Problem

- **ID**: euler-identity-oq-01-oq-04
- **Name**: Extend Euler identity proof to full group isomorphism ℝ/2πℤ ≅ S¹
- **Tier**: B
- **Significance**: 6/10
- **Tractability**: 7/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Top composite score among quality-passing candidates after domain-diversity filtering**: Composite = 76 (EMPTY tier: 0 penalty + tractability×10=70 + significance=6). mean-value-theorem-oq-04 (score 77) was already selected in a prior run today; divisibility-rules-oq-03 (also 76) was deprioritized due to diversity penalty — last 3 selections were from number theory/algebra domains.
2. **EMPTY knowledge tier**: No prior research accumulated — fresh territory warranting immediate exploration.
3. **Domain diversity**: Complex analysis / Lie group theory, distinct from recent number theory selections (euler-totient, prime-gap-bounds, mathematical-induction).
4. **Substantive mathematics**: The group isomorphism ℝ/2πℤ ≅ S¹ via Euler's exponential map touches Lie group theory (exp: ℝ → S¹ as a Lie group homomorphism), the quotient group structure of the circle, and Mathlib's `Complex.expMapCircle` / `AddCircle` API. Non-trivial formalization target.

## Rejection Summary

- **Candidates considered**: 17 available
- **Candidates rejected**: 16
  - mean-value-theorem-oq-04 (score 77): already initialized via prior seeker run today
  - divisibility-rules-oq-03 (score 76): diversity penalty — number theory, same domain as last 3 selections
  - isosceles-triangle-oq-03 (score 85 raw): C-tier, formula derivation with no theory-level implications — rejected as one-off example check
  - minkowski-fundamental-theorem-oq-02 (score 68): algebraic number theory — diversity penalty applies
  - hilbert-17-oq-04, lovasz-local-lemma-oq-02/03, szemeredi-counting-oq-01 (scores 67): lower composite scores
  - remaining: lower composite scores
- **Confidence**: high (clear score gap: selected at 76, next-best at 68 after diversity adjustments)

## Lean Context

The open question from the `euler-identity-oq-01` gallery proof:

> "Can the Lean proof be extended to give the full group isomorphism ℝ/2πℤ ≅ S¹ by viewing Euler's formula as the exponential map of the Lie group ℝ?"

Key Mathlib APIs to investigate:
- `Complex.expMapCircle`: the surjective homomorphism `ℝ → circle`, defined by `t ↦ exp(it)`
- `Complex.exp_periodic`: periodicity 2πi of `Complex.exp`
- `AddCircle`: `ℝ ⧸ (p • ℤ)` — the additive quotient group construction
- `AddCircle.homeomorphCircle`: homeomorphism `AddCircle (2 * π) ≃ₜ circle`
- `QuotientAddGroup.quotientKerEquivRange`: first isomorphism theorem for additive groups
- `MonoidHom.ker`: kernel of `Complex.expMapCircle`

## Related Gallery Proofs

- `euler-identity`: base formalization of e^(iπ) + 1 = 0
- `euler-identity-oq-01`: extended via Taylor series tsum for cos and sin
- `euler-identity-oq-01-oq-01`, `-oq-02`, `-oq-03`: prior open question chains on this thread

## Suggested First Steps

1. **OBSERVE**: Read `proofs/Proofs/EulerIdentityOQ01.lean`; search Mathlib for `expMapCircle`, `AddCircle`, `circle` to map the API landscape
2. **ORIENT**: Determine whether `AddCircle.homeomorphCircle` or `QuotientAddGroup.quotientKerEquivRange expMapCircle` already yields the isomorphism; check if the kernel of `expMapCircle` is provably `(2 * π) • ℤ`
3. **DECIDE**: If Mathlib infrastructure is sufficient, write a clean wrapper theorem; if kernel computation requires work, identify the minimal sorry-free path

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 17 |
| In Progress | 509 |
| Completed | 1236 |
| Blocked | 2 |
| **Total** | **1764** |

## Candidate Pool Health

- Pool depth: **adequate** (17 available > threshold of 5)
- Confidence: high — clear score separation between selected and next-best candidates
- Recommendation: Pool healthy; no replenishment needed
- Next refresh recommended: when available count drops below 5
