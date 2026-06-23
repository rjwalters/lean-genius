# Problem Selection Report

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 84 available, 1257 in-progress, 589 completed, 7 graduated

## Selected Problem

- **ID**: ptolemys-theorem-oq-01-oq-01
- **Name**: Ptolemy Converse: Equality Characterizes Cyclic Quadrilaterals
- **Tier**: B
- **Significance**: 8/10
- **Tractability**: 7/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **High significance + tractability balance (score 78)**: sig=8 paired with tract=7 puts this in the top tier of currently available problems. The Ptolemy converse is a complete, well-stated result — not an open conjecture, not a shallow example.
2. **Direct parent proof available**: `ptolemys-theorem-oq-01` (forward direction, 0 sorries, verified) lives in the gallery. The converse reuses the same complex-number setup. Proof sketch: any four points satisfying equality in Ptolemy's inequality must lie on a common circle in cyclic order; this follows from the equality case of the Ptolemy inequality which factors as `|z₁z₄ - z₂z₃| ≤ |z₁ - z₂||z₃ - z₄| + |z₂ - z₃||z₁ - z₄|` with equality iff the cross-ratio is real.
3. **Domain diversity**: Classical Euclidean geometry / complex number geometry — not covered in the three most recent seeker batches (Szemerédi combinatorics, isoperimetric differential geometry, p-adic analysis).

## Quality Gate

- Near-duplicate of recent completions? **No** — `ptolemys-theorem-oq-01` proved the forward direction; this proves the converse (bidirectional = strictly stronger).
- Shallow specialization? **No** — completing a biconditional characterization is theory-level.
- One-off example check? **No** — holds for any four distinct points on any circle.
- Significance ≥ 3? **Yes** (8/10).
- Last 3 selections same domain? **No** — geometry was not in the last three problem domains.

## Rejection Summary

- **Candidates considered**: 84
- **Candidates rejected**: moonshots (tractability ≤ 2: Goldbach, twin primes, Sophie Germain), Szemerédi diversity penalty (3 Szemerédi problems in recent batches), C-tier low-significance candidates (arithmetic-series nested, divisibility-by-3 nested)
- **Confidence**: high (score 78 shared with lebesgue-measure-oq-03-oq-01; both selected this batch)

## Related Gallery Proofs

- `ptolemys-theorem-oq-01`: Forward direction — equality for CCW cyclic order. Direct parent.
- `ptolemys-theorem`: Classical Ptolemy's theorem via complex numbers.
- `ptolemys-complex-proof-oq-01`: Complex number proof variant — same infrastructure.

## Suggested First Steps

1. **OBSERVE**: Read `ptolemys-theorem-oq-01` and `ptolemys-theorem` Lean sources. Map the complex-number setup (`z₁, z₂, z₃, z₄ ∈ S¹`) and the Ptolemy inequality proof to identify where the equality case is characterized.
2. **ORIENT**: Search Mathlib for `ptolemy_inequality` equality case lemmas. Check if `Complex.abs_add_mul_self_le` or cross-ratio lemmas exist. Look for `inscribed_angle` or `cyclic_order` machinery.
3. **DECIDE**: The equality `AC·BD = AB·CD + AD·BC` in complex terms means `|z₁-z₃||z₂-z₄| = |z₁-z₂||z₃-z₄| + |z₁-z₄||z₂-z₃|`. Equality in the Ptolemy inequality holds iff the cross-ratio `(z₁-z₃)(z₂-z₄)/((z₁-z₂)(z₃-z₄))` is real and positive — which characterizes cyclic order on a circle.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 84 |
| In Progress | 1257 |
| Completed | 589 |
| Graduated | 7 |
| Blocked | 2 |

## Candidate Pool Health

Pool is **adequate** (84 >> threshold 15). No replenishment needed this cycle.

- Pool depth: adequate
- Recommendation: Pool healthy; continue periodic checks
- Next refresh recommended: 30 minutes

## Initialized

- [x] Research workspace exists at `research/problems/ptolemys-theorem-oq-01-oq-01/`
- [x] problem.md populated with formal statement and context
- [x] Registered in `research/db/knowledge.db` with status 'available'
- [x] Ready for /researcher
