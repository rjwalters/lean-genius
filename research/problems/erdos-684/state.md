# Current State

**Phase**: ACT
**Since**: 2026-01-14T19:46:33.194Z
**Iteration**: 5
**Last Update**: 2026-06-14 (researcher-4 — binomial u·v decomposition)

## Current Focus

`Erdos684Problem.lean` formalizes smooth/rough parts of binomial coefficients and f(n) = min k with k-smooth part of C(n,k) > n². This session added the central u·v decomposition for the binomial-specific definitions (the file defined `binomialRoughPart` but never proved the factorization) and realigned the badly-drifted gallery meta sections.

## Status Summary

| Surface | Value | Source |
|---------|-------|--------|
| Lean file | `proofs/Proofs/Erdos684Problem.lean` (462 LOC, 22 thm, 11 def, 2 axioms, 0 sorries) | `wc -l` + grep |
| Axioms | `f_domain_large`, `mahler_ineffective` | `grep '^axiom '` |
| Gallery | `src/data/proofs/erdos-684/meta.json` — `axiomCount: 2`, `theoremCount: 22`, sections realigned (were drifted, ended @401 of 462-line file) | `meta.json` |

## Active Approach

Structural completeness — formalizing the decomposition objects the problem is stated in terms of. Added `binomial_smooth_rough_decomposition` (C(n,k) = smooth·rough) and `binomialSmoothPart_dvd` as instantiations of the proven general `smooth_rough_decomposition`/`smoothPart_dvd`.

## Blockers

- `f_domain_large` — existence threshold N₀ above which {k | smoothPart > n²} is nonempty; needs a concrete witness/estimate (C(n,⌊n/2⌋) grows like 2ⁿ/√n).
- `mahler_ineffective` — Mahler's ineffective bound smoothPart ≤ n^{1+ε}; deep, not in Mathlib.

## Next Action

Reducing `f_domain_large` requires an explicit n₀ where smoothPart of C(n₀,⌊n₀/2⌋) exceeds n₀² — a real computation (build-gated). Structural decomposition now complete.

## Attempt Counts

- Total attempts: 5
- Current approach attempts: 1
- Approaches tried: 2

## Iteration Ledger

| Iter | Date | Agent | Result | Scope |
|------|------|-------|--------|-------|
| 1–4 | 2026-01–06 | (legacy) | Built smoothPart/roughPart, Kummer/Legendre, f(n), Mahler→f→∞ chain; 20 thm, 2 axioms | Erdos684Problem.lean |
| 5 | 2026-06-14 | researcher-4 | Added `binomial_smooth_rough_decomposition` + `binomialSmoothPart_dvd`; thm 20→22, LOC 451→462; realigned drifted meta sections; build-pending (Docker down) | Erdos684Problem.lean + meta.json + registry + state.md |

## Cross-references

- Research JSON registry: `src/data/research/problems/erdos-684.json`
- Gallery dir: `src/data/proofs/erdos-684/`
- Lean source: `proofs/Proofs/Erdos684Problem.lean`
