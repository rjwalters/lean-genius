# Problem: Erdős #891

## Statement

### Plain Language
Let $2=p_1k$ many prime factors?



Schinzel deduced from P\'{o}lya's theorem \cite{Po18} (that the sequence of $k$-smooth integers has unbounded gaps) that this is true with $p_1\cdots p_k$ replaced by $p_1\cdots p_{k-1}p_{k+1}$.

This is unknown even for $k=2$ - that is, is it true that in every interval of $6$ (sufficiently large) consecutive integers there must exist one with at least $3$ prime factors?

Weisenberg ha...


### Formal Statement
$$
Let $2=p_1<p_2<\cdots$ be the primes and $k\geq 2$. Is it true that, for all sufficiently large $n$, there must exist an integer in $[n,n+p_1\cdots p_k)$ with $>k$ many prime factors?



Schinzel deduced from P\'{o}lya's theorem \cite{Po18} (that the sequence of $k$-smooth integers has unbounded gaps) that this is true with $p_1\cdots p_k$ replaced by $p_1\cdots p_{k-1}p_{k+1}$.

This is unknown even for $k=2$ - that is, is it true that in every interval of $6$ (sufficiently large) consecutive integers there must exist one with at least $3$ prime factors?

Weisenberg has observed that Dickson's conjecture implies the answer is no if we replace $p_1\cdots p_k$ with $p_1\cdots p_k-1$. Indeed, let $L_k$ be the lowest common multiple of all integers at most $p_1\cdots p_k$. By Dickson's conjecture there are infinitely many $n'$ such that $\frac{L_k}{m}n'+1$ is prime for all $1\leq m<p_1\cdots p_k$. It follows that, if $n=L_kn'+1$, then all integers in $[n,n+p_1\cdots p_k-1)$ have at most $k$ prime factors.
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 891
erdosUrl: https://erdosproblems.com/891

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
- [Problem #890](https://www.erdosproblems.com/890)
- [Problem #892](https://www.erdosproblems.com/892)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Po18]

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
