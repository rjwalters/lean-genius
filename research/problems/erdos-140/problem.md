# Problem: Erdos #140

## Statement

### Plain Language
Let r_3(N) be the size of the largest subset of {1,...,N} which does not contain a non-trivial 3-term arithmetic progression. Prove that r_3(N) << N/(log N)^C for every C > 0.

### Formal Statement
$$
\forall C > 0, \exists K > 0 : \forall N \geq 3, r_3(N) \leq K \cdot \frac{N}{(\log N)^C}
$$

## Classification

```yaml
tier: A
significance: 9
tractability: 10
erdosNumber: 140
erdosUrl: https://erdosproblems.com/140
prize: $500

tags:
  - erdos
  - additive-combinatorics
  - arithmetic-progressions
  - density
```

**Significance**: 9/10 (Major breakthrough in additive combinatorics)
**Tractability**: 10/10 (SOLVED by Kelley-Meka 2023)
**Prize**: $500

## Why This Matters

1. **Roth's Theorem Generalization** - Extends seminal result on 3-AP density
2. **Breakthrough Achievement** - Kelley-Meka (2023) resolved 70-year-old problem
3. **Additive Combinatorics Cornerstone** - Central result in the field
4. **Prize Problem** - One of Erdos's famous cash prize problems

## Key Results

- **Roth (1953)**: r_3(N) = o(N) - first breakthrough
- **Bourgain (2008)**: O(N / (log log N)^{1/2})
- **Sanders (2011)**: O(N (log log N)^5 / log N)
- **Bloom-Sisask (2020)**: O(N / (log N)^{1+c}) for some c > 0
- **Kelley-Meka (2023)**: O(N / (log N)^C) for ALL C > 0 - SOLVED

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| Erdos140Problem.lean | Full formalization with Kelley-Meka theorem |

## References

- Roth, K.F. (1953): "On certain sets of integers"
- Kelley, Z., Meka, R. (2023): "Strong bounds for 3-progressions"
- Bloom, T., Sisask, O. (2020): "Breaking the logarithmic barrier in Roth's theorem"

---

*Last updated: 2026-01-14*
