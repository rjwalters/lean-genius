# Problem: Erdos #135

## Statement

### Plain Language
Let A be a set of n points in ℝ² such that any subset of 4 points determines at least 5 distinct distances. Must A determine ≫ n² (i.e., Ω(n²)) distinct distances?

### Formal Statement
$$
\forall A \subset \mathbb{R}^2, |A|=n, (\forall p_1,p_2,p_3,p_4 \in A : |\{d(p_i,p_j)\}| \geq 5) \Rightarrow |D(A)| = \Omega(n^2)?
$$

## Classification

```yaml
tier: B
significance: 8
tractability: 10
erdosNumber: 135
erdosUrl: https://erdosproblems.com/135
prize: $250

tags:
  - erdos
  - combinatorial-geometry
  - distance-problems
  - disproved
```

**Significance**: 8/10 (Solved by Terence Tao, fundamental in distance geometry)
**Tractability**: 10/10 (DISPROVED by Tao 2024)
**Prize**: $250

## Why This Matters

1. **Tao's Solution** - Part of Tao's 2024-2025 sweep through Erdős problems
2. **Algebraic-Probabilistic Method** - Elegant combination of algebraic curves and randomization
3. **Connection to Guth-Katz** - Related to distinct distances problem (different exponent)
4. **AI Exploration** - Tao mentioned exploring for AI-suitable problems when finding this

## Key Results

- **Erdős-Gyárfás**: Original conjecture that Ω(n²) distances should be required
- **Tao (2024)**: Constructed counterexample with O(n²/√log n) distances
- **Key insight**: Randomized parabolas over finite fields avoid forbidden patterns

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| Erdos135Problem.lean | Full formalization with Tao's disproof |

## References

- Tao (2024): arXiv:2409.01343 "Planar point sets with forbidden 4-point patterns"
- Erdős-Gyárfás: Original conjecture
- Guth-Katz (2015): Lower bound for distinct distances

---

*Last updated: 2026-01-14*
