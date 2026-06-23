# Problem: Erdős #450

## Statement

### Plain Language
How large must $y=y(\epsilon,n)$ be such that the number of integers in $(x,x+y)$ with a divisor in $(n,2n)$ is at most $\epsilon y$?



It is not clear what the intended quantifier on $x$ is. Cambie has observed that if this is intended to hold for all $x$ then, provided\[\epsilon(\log n)^\delta (\log\log n)^{3/2}\to \infty\]as $n\to \infty$, where $\delta=0.086\cdots$, there is no such $y$, which follows from an averagi...


### Formal Statement
$$
How large must $y=y(\epsilon,n)$ be such that the number of integers in $(x,x+y)$ with a divisor in $(n,2n)$ is at most $\epsilon y$?



It is not clear what the intended quantifier on $x$ is. Cambie has observed that if this is intended to hold for all $x$ then, provided\[\epsilon(\log n)^\delta (\log\log n)^{3/2}\to \infty\]as $n\to \infty$, where $\delta=0.086\cdots$, there is no such $y$, which follows from an averaging argument and the work of Ford \cite{Fo08}.

On the other hand, Cambie has observed that if $\epsilon\ll 1/n$ then $y(\epsilon,n)\sim 2n$: indeed, if $y<2n$ then this is impossible taking $x+n$ to be a multiple of the lowest common multiple of $\{n+1,\ldots,2n-1\}$. On the other hand, for every fixed $\delta\in (0,1)$ and $n$ large every $2(1+\delta)n$ consecutive elements contains many elements which are a multiple of an element in $(n,2n)$.
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 450
erdosUrl: https://erdosproblems.com/450

tags:
  - erdos
```

**Significance**: 6/10
**Tractability**: 4/10

## Why This Matters

1. **Erdős Legacy** - Part of Paul Erdős's influential problem collection
2. **Mathematical significance** - open problem


## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| --- | --- |

## Related Problems

- [Problem #2000](https://www.erdosproblems.com/2000)
- [Problem #83](https://www.erdosproblems.com/83)
- [Problem #888](https://www.erdosproblems.com/888)
- [Problem #1998](https://www.erdosproblems.com/1998)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #449](https://www.erdosproblems.com/449)
- [Problem #451](https://www.erdosproblems.com/451)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Fo08]

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
