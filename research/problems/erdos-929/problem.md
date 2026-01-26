# Problem: Erdős #929

## Statement

### Plain Language
Let $k\geq 2$ be large and let $S(k)$ be the minimal $x$ such that there is a positive density set of $n$ where\[n+1,n+2,\ldots,n+k\]are all divisible by primes $\leq x$.

Estimate $S(k)$ - in particular, is it true that $S(k)\geq k^{1-o(1)}$?



It follows from Rosser's sieve that $S(k)> k^{1/2-o(1)}$.

It is trivial that $S(k)\leq k+1$ since, for example, one can take $n\equiv 1\pmod{(k+1)!}$. The best bound on large ga...


### Formal Statement
$$
Let $k\geq 2$ be large and let $S(k)$ be the minimal $x$ such that there is a positive density set of $n$ where\[n+1,n+2,\ldots,n+k\]are all divisible by primes $\leq x$.

Estimate $S(k)$ - in particular, is it true that $S(k)\geq k^{1-o(1)}$?



It follows from Rosser's sieve that $S(k)> k^{1/2-o(1)}$.

It is trivial that $S(k)\leq k+1$ since, for example, one can take $n\equiv 1\pmod{(k+1)!}$. The best bound on large gaps between primes due to Ford, Green, Konyagin, Maynard, and Tao \cite{FGKMT18} (see [4]) implies\[S(k) \ll k \frac{\log\log\log k}{\log\log k\log\log\log\log k}.\]
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 929
erdosUrl: https://erdosproblems.com/929

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
- [Problem #4](https://www.erdosproblems.com/4)
- [Problem #928](https://www.erdosproblems.com/928)
- [Problem #930](https://www.erdosproblems.com/930)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Er76d]
- [FGKMT18]

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
