# Problem: Erdos #31

## Statement

### Plain Language
Given any infinite set A ⊂ ℕ, there exists a set B of density 0 such that A + B contains all except finitely many positive integers.

### Formal Statement
$$
\forall A \subseteq \mathbb{N} \text{ infinite}, \exists B \subseteq \mathbb{N} : d(B) = 0 \land |(\mathbb{N} \setminus (A+B)) \cap \mathbb{N}^+| < \infty
$$

## Classification

```yaml
tier: B
significance: 7
tractability: 7
erdosNumber: 31
erdosUrl: https://erdosproblems.com/31

tags:
  - erdos
  - additive-combinatorics
  - density
  - sumsets
```

**Significance**: 7/10
**Tractability**: 7/10 (SOLVED by Lorentz 1954)

## Why This Matters

1. **Additive Structure** - Shows any infinite set can "complete" ℕ with a sparse complement
2. **Density Theory** - Fundamental result about density-0 sets and additive bases
3. **Erdős-Straus Conjecture** - Original conjecture by Erdős and Straus

## Key Results

- **Lorentz (1954)**: PROVED the conjecture
- Strengthened: B can be chosen with |B ∩ [1,N]| = O(N/log N)

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| Erdos31Problem.lean | Full formalization with Lorentz theorem |
| Erdos109Problem.lean | Related sumset density results |

## References

- Lorentz, G.G. (1954): "On a problem of additive number theory"
- Erdős-Straus: Original conjecture

---

*Last updated: 2026-01-14*
