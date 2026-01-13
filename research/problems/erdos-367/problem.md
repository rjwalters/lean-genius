# Problem: Erdős #367

## Statement

### Plain Language
Forum
Favourites
Tags
More
 Go
 Go
Dual View
Random Solved
Random Open

Let $B_2(n)$ be the 2-full part of $n$ (that is, $B_2(n)=n/n'$ where $n'$ is the product of all primes that divide $n$ exactly once). Is it true that, for every fixed $k\geq 1$,\[\prod_{n\leq m0$,\[\limsup \frac{\prod_{n\leq m<n+k}B_r(m) }{n^{1+\epsilon}}\to\infty?\]van Doorn notes in the comments that for $k\leq 2$ we trivially have\[\prod_{n\leq m<n+k}B_2(m) \ll n^{2},\]but that this fails for all $k\geq 3$, and in fact...

### Formal Statement
$$
Forum
Favourites
Tags
More
 Go
 Go
Dual View
Random Solved
Random Open

Let $B_2(n)$ be the 2-full part of $n$ (that is, $B_2(n)=n/n'$ where $n'$ is the product of all primes that divide $n$ exactly once). Is it true that, for every fixed $k\geq 1$,\[\prod_{n\leq m<n+k}B_2(m) \ll n^{2+o(1)}?\]Or perhaps even $\ll_k n^2$?



It would also be interesting to find upper and lower bounds for the analogous product with $B_r$ for $r\geq 3$, where $B_r(n)$ is the $r$-full part of $n$ (that is, the product of prime powers $p^a \mid n$ such that $p^{a+1}\nmid n$ and $a\geq r$). Is it true that, for every fixed $r,k\geq 2$ and $\epsilon>0$,\[\limsup \frac{\prod_{n\leq m<n+k}B_r(m) }{n^{1+\epsilon}}\to\infty?\]van Doorn notes in the comments that for $k\leq 2$ we trivially have\[\prod_{n\leq m<n+k}B_2(m) \ll n^{2},\]but that this fails for all $k\geq 3$, and in fact\[\prod_{n\leq m<n+3}B_2(m) \gg n^{2}\log n\]infinitely often.


Back to the problem
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 367
erdosUrl: https://erdosproblems.com/367

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
- [Problem #366](https://www.erdosproblems.com/366)
- [Problem #368](https://www.erdosproblems.com/368)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

(No references available)

## OEIS Sequences

- [A057521](https://oeis.org/A057521)
- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
