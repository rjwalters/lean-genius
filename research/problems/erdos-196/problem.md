# Problem: Erdos #196

## Statement

### Plain Language
Must every permutation of the natural numbers contain a monotone 4-term arithmetic progression?

A monotone AP means either indices i < j < k < l with x_i, x_j, x_k, x_l in AP, or indices i > j > k > l with the same AP property.

### Formal Statement
$$
\forall x : \mathbb{N} \to \mathbb{N} \text{ bijection}, \exists i,j,k,l \in \mathbb{N}:
(i < j < k < l \lor i > j > k > l) \land (x_j - x_i = x_k - x_j = x_l - x_k)
$$

## Classification

```yaml
tier: B
significance: 7
tractability: 5
erdosNumber: 196
erdosUrl: https://erdosproblems.com/196

tags:
  - erdos
  - combinatorics
  - permutations
  - arithmetic-progressions
```

**Significance**: 7/10
**Tractability**: 5/10 (OPEN problem, boundary case between k=3 proved and k=5 disproved)

## Why This Matters

1. **Boundary Problem** - Critical threshold between k=3 (always exists) and k=5 (counterexample exists)
2. **Combinatorics** - Connects permutation theory with arithmetic progressions
3. **Erdos Legacy** - Part of Paul Erdos's influential problem collection

## Key Results

- **DEGS (1977)**: k=3 always exists (proved)
- **DEGS (1977)**: k=5 can be avoided (counterexample construction)
- **k=4**: OPEN - the main conjecture

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| Erdos196Problem.lean | Full formalization with k=3,4,5 definitions |

## Related Problems

- [Problem #194](https://www.erdosproblems.com/194)
- [Problem #195](https://www.erdosproblems.com/195)

## References

- Davis, Entringer, Graham, Simmons (1977): "Monotone subsequences and arithmetic progressions"

---

*Last updated: 2026-01-14*
