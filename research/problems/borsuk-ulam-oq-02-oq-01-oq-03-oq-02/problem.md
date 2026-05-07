# Problem: For S_n, is symBUDim n d = buDim_{largest prime ≤ n} d = 2⌊d/2⌋ − 1?

## Statement

### Plain Language

For the symmetric group S_n acting on a d-dimensional real representation,
is the equivariant Borsuk-Ulam dimension equal to `buDim p* d`, where p* is
the largest prime ≤ n? On even dimensions d = 2k this conjectural value is
2k − 1, matching the Yang-Borsuk formula for cyclic prime groups.

### Formal Statement

For every n ≥ 2 and d ≥ 1,
$$
  \text{symBUDim}(n, d) \stackrel{?}{=} \text{buDim}(p^*, d) = 2 \lfloor d/2 \rfloor - 1,
$$
where $p^* = \max\{p \text{ prime} : p \leq n\}$.

## Classification

```yaml
tier: B
significance: 6
tractability: 6
tags:
  - seeker-selected
  - borsuk-ulam
  - equivariant-topology
  - symmetric-groups
  - open-conjecture
```

**Significance**: 6/10
**Tractability**: 6/10

## Why This Matters

1. **Equivariant topology gap**: A direct proof would require Fadell-Husseini
   cohomological index for non-cyclic groups, which is currently outside
   Mathlib. Either a positive result or a counterexample would close a
   meaningful gap in the formalized equivariant topology library.
2. **Practical value**: Resolving the conjecture would yield the explicit
   closed form `symBUDim n (2k) = 2k − 1` for all S_n, simplifying
   downstream applications (chromatic-number bounds via Lovász-Kneser, etc.).
3. **Test cases at small n**: The conjecture is most interesting at n with
   rich non-cyclic subgroup structure: n = 4 (V₄ ≤ S₄), n = 8
   (S₈ contains V₄, A₄, multiple non-cyclic factors).

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| borsuk-ulam-oq-02-oq-01-oq-03 | Parent: develops the symBUDim framework with subgroup monotonicity. |
| borsuk-ulam-oq-02-oq-01 | Cyclic-group buDim (buDim_prime, buDim_mono, buDim_two). |
| bertrands-postulate | Used in Iteration 3 to prove `n/2 < largestPrimeBelow n`. |

## Status (2026-05-08)

- Phase-2 axiomatization is complete:
  - `largestPrimeBelow n := Nat.findGreatest Nat.Prime n` (def + 3 supporting facts)
  - `symBUDim_eq_largestPrime` (single axiom, the open content)
  - `symBUDim_even_formula` (closed form, conditional)
  - `symBUDim_even_lower` (UNCONDITIONAL lower bound)
  - 3 concrete instances at S_3, S_4, S_5
  - Bertrand bound `n/2 < largestPrimeBelow n` (added in iteration 3)
- Lean file: `proofs/Proofs/BorsukUlamOQ02OQ01OQ03OQ02.lean`, 241 lines, 1 axiom.
- Gallery: `src/data/proofs/borsuk-ulam-oq-02-oq-01-oq-03-oq-02/`.
