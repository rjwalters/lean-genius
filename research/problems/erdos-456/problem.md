# Problem: Erdős #456

## Statement

### Plain Language
Let $p_n$ be the smallest prime $\equiv 1\pmod{n}$ and let $m_n$ be the smallest integer such that $n\mid \phi(m_n)$.

Is it true that $m_n<p_n$ for almost all $n$? Does $p_n/m_n\to \infty$ for almost all $n$? Are there infinitely many primes $p$ such that $p-1$ is the only $n$ for which $m_n=p$?



Linnik's theorem implies that $p_n\leq n^{O(1)}$. It is trivial that $m_n\leq p_n$ always.

If $n=q-1$ for some prime $q$ th...


### Formal Statement
$$
Let $p_n$ be the smallest prime $\equiv 1\pmod{n}$ and let $m_n$ be the smallest integer such that $n\mid \phi(m_n)$.

Is it true that $m_n<p_n$ for almost all $n$? Does $p_n/m_n\to \infty$ for almost all $n$? Are there infinitely many primes $p$ such that $p-1$ is the only $n$ for which $m_n=p$?



Linnik's theorem implies that $p_n\leq n^{O(1)}$. It is trivial that $m_n\leq p_n$ always.

If $n=q-1$ for some prime $q$ then $m_n=p_n$. Erd\H{o}s \cite{Er79e} writes it is 'easy to show' that for infinitely many $n$ we have $m_n <p_n$, and that $m_n/n\to \infty$ for almost all $n$.

van Doorn in the comments has noted that if $n=2^{2k+1}$ then $m_n\leq 2n$ and $p_n\geq 2n+1$.
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 456
erdosUrl: https://erdosproblems.com/456

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
- [Problem #455](https://www.erdosproblems.com/455)
- [Problem #457](https://www.erdosproblems.com/457)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Er79e]

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
