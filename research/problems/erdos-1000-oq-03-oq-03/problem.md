# Problem: Do the closed forms transfer to Jordan's higher totient J_k, where Σ_{d|n} J_...

**Slug**: erdos-1000-oq-03-oq-03
**Created**: 2026-07-01
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Plain Language

Do the closed forms transfer to Jordan's higher totient J_k, where Σ_{d|n} J_k(d) = n^k, giving restricted sums equal to (ordCompl[p] n)^k?

### Why This Matters

This is an open-question extension (generalization) arising from the gallery proof
"Erdős #1000 OQ-03: Generalized Totients with Restricted Denominator Conditions" (erdos-1000-oq-03). It records a natural next step flagged during
formalization: Do the closed forms transfer to Jordan's higher totient J_k, where Σ_{d|n} J_k(d) = n^k, giving restricted sums equal to (ordCompl[p] n)^k?

Estimated tractability: challenging.

## Known Results

### What's Already Proven

- Parent gallery proof: Erdős #1000 OQ-03: Generalized Totients with Restricted Denominator Conditions (`erdos-1000-oq-03`) — provides the base result and
  the machinery this extension builds on.

### What's Still Open

- Do the closed forms transfer to Jordan's higher totient J_k, where Σ_{d|n} J_k(d) = n^k, giving restricted sums equal to (ordCompl[p] n)^k?

### Our Goal

Formalize the statement above in Lean 4, reusing the parent proof's development
where possible and filling the specific gap this open question identifies.

## Related Gallery Proofs

- `erdos-1000-oq-03` — parent proof / direct source of this open question.

## Tags

number-theory, totient-function, gauss-identity, divisor-sums, generalized-totient, erdos
