# Problem: Erdős #1055

## Statement

### Plain Language
A prime $p$ is in class $1$ if the only prime divisors of $p+1$ are $2$ or $3$. In general, a prime $p$ is in class $r$ if every prime factor of $p+1$ is in some class $\leq r-1$, with equality for at least one prime factor.

Are there infinitely many primes in each class? If $p_r$ is the least prime in class $r$, then how does $p_r^{1/r}$ behave?



A classification due to Erd\H{o}s and Selfridge. It is easy to prove tha...


### Formal Statement
$$
A prime $p$ is in class $1$ if the only prime divisors of $p+1$ are $2$ or $3$. In general, a prime $p$ is in class $r$ if every prime factor of $p+1$ is in some class $\leq r-1$, with equality for at least one prime factor.

Are there infinitely many primes in each class? If $p_r$ is the least prime in class $r$, then how does $p_r^{1/r}$ behave?



A classification due to Erd\H{o}s and Selfridge. It is easy to prove that the number of primes $\leq n$ in class $r$ is at most $n^{o(1)}$.

The sequence $p_r$ begins $2,13,37,73,1021$ (A005113 in the OEIS). Erd\H{o}s thought $p_r^{1/r}\to \infty$, while Selfridge thought it quite likely to be bounded.

A similar question can be asked replacing $p+1$ with $p-1$.

This is problem A18 in Guy's collection \cite{Gu04}.
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 1055
erdosUrl: https://erdosproblems.com/1055

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
- [Problem #1054](https://www.erdosproblems.com/1054)
- [Problem #1056](https://www.erdosproblems.com/1056)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Er77]
- [Gu04]

## OEIS Sequences

- [A005113](https://oeis.org/A005113)
- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
