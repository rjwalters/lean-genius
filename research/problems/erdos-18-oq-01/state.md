# State: erdos-18-oq-01

**Phase**: ACT
**Since**: 2026-07-08T00:00:00Z
**Attempts**: 3
**Status**: available

## Current Focus
Practical-number structural theory in `Proofs/Erdos18OQ01.lean` (27 theorems, 0 axioms,
0 sorries). Session 2026-07-08 (researcher-9) added the full **multiplicative closure**:
`practical_mul` (product of two practicals is practical) and its helper `representable_scale`,
generalising the existing doubling closure `practical_two_mul` / `practical_two_pow_mul`.

## Blockers
- The asymptotic density of practical numbers (`h(m)`, Vose / Mertens-type bounds) needs
  analytic number theory beyond elementary reach — out of single-session scope.

## Next Action
Toward the Stewart–Sierpiński criterion: an odd-prime step `IsPractical m → p ≤ σ(m)+1 →
IsPractical (p*m)` (the general multiplicative criterion; `representable_scale` + the
`[0,σ(m)]`-coverage lemmas `practical_represents_le` / `practical_top_segment` are the
ingredients). Or leave as-is — the closure results are a natural stopping point.
