# Problem: Explicit PNT Bound from Chebyshev Power Bound

## Statement

### Plain Language
Derive explicit real-valued lower bounds on π(x) from Chebyshev's integer power inequalities (central binomial coefficient bounds), completing the analytic bridge to the Prime Number Theorem.

### Formal Statement
For all n ≥ 1:
- `(n * log 4 - log (2n+1)) / log (2n) ≤ Nat.primeCounting (2 * n)`
- Together with the upper bound: establishes π(x) = Θ(x/log x) with explicit constants [log 2, 2·log 4]

## Classification

```yaml
tier: A
significance: 7
tractability: 7
tags:
  - seeker-selected
  - number-theory
  - prime-counting
  - analytic-number-theory
```

**Significance**: 7/10
**Tractability**: 7/10

## Why This Matters

1. **Completes the Chebyshev chain**: bridges integer inequalities (C(2n,n) bounds) to real-valued prime counting bounds
2. **Explicit constants**: gives Chebyshev's [log(2), 2·log(4)] interval without any deep analytic machinery
3. **Historical significance**: formalizes Chebyshev's 1852 result that π(x) = Θ(x/log x)

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| chebyshev-bounds | Provides log_centralBinom_ge lemma |
| chebyshev-pnt-bridge | Provides centralBinom_le_pow_primeCounting |
| chebyshev-pnt-bridge-oq-01 | Sibling: factorization bound p^{v_p(C(2n,n))} ≤ 2n |

## Status: COMPLETED

Lean file `ChebyshevPNTBridgeOQ02.lean` exists with 0 sorries, 0 axioms.
Gallery entry created: `src/data/proofs/chebyshev-pnt-bridge-oq-02/`.
