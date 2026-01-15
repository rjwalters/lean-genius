# Problem: Erdős #890

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

If $\omega(n)$ counts the number of distinct prime factors of $n$, then is it true that, for every $k\geq 1$,\[\liminf_{n\to \infty}\sum_{0\leq ik$ by P\'{o}lya's theorem.

It is a classical fact that\[\limsup_{n\to \infty}\omega(n)\frac{\log\log n}{\log n}=1.\]




References


[ErSe67] Erd\H{o}s, P. and Selfridge, J. L., Some problems on the prime factors of consecutive integers. Illinois J. Math. (1967), 428--430.


Ba...

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

If $\omega(n)$ counts the number of distinct prime factors of $n$, then is it true that, for every $k\geq 1$,\[\liminf_{n\to \infty}\sum_{0\leq i<k}\omega(n+i)\leq k+\pi(k)?\]Is it true that\[\limsup_{n\to \infty}\left(\sum_{0\leq i<k}\omega(n+i)\right) \frac{\log\log n}{\log n}=1?\]



A question of Erd\H{o}s and Selfridge \cite{ErSe67}, who observe that\[\liminf_{n\to \infty}\sum_{0\leq i<k}\omega(n+i)\geq k+\pi(k)-1\]for every $k$. This follows from P\'{o}lya's theorem that the set of $k$-smooth integers has unbounded gaps - indeed, $n(n+1)\cdots (n+k-1)$ is divisible by all primes $\leq k$ and, provided $n$ is large, all but at most one of $n,n+1,\ldots,n+k-1$ has a prime factor $>k$ by P\'{o}lya's theorem.

It is a classical fact that\[\limsup_{n\to \infty}\omega(n)\frac{\log\log n}{\log n}=1.\]




References


[ErSe67] Erd\H{o}s, P. and Selfridge, J. L., Some problems on the prime factors of consecutive integers. Illinois J. Math. (1967), 428--430.


Back to the problem
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 890
erdosUrl: https://erdosproblems.com/890

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
- [Problem #889](https://www.erdosproblems.com/889)
- [Problem #891](https://www.erdosproblems.com/891)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [ErSe67]

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
