# Problem: Erdős #563

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

Let $F(n,\alpha)$ denote the largest $m$ such that there exists a $2$-colouring of the edges of $K_n$ so that every $X\subseteq [n]$ with $\lvert X\rvert\geq m$ contains more than $\alpha \binom{\lvert X\rvert}{2}$ many edges of each colour.

Prove that, for every $0\leq \alpha\leq 1/2$,\[F(n,\alpha)\sim c_\alpha\log n\]for some constant $c_\alpha$ depending only on $\alpha$.



It is easy to show that, for every $0\leq \...

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

Let $F(n,\alpha)$ denote the largest $m$ such that there exists a $2$-colouring of the edges of $K_n$ so that every $X\subseteq [n]$ with $\lvert X\rvert\geq m$ contains more than $\alpha \binom{\lvert X\rvert}{2}$ many edges of each colour.

Prove that, for every $0\leq \alpha\leq 1/2$,\[F(n,\alpha)\sim c_\alpha\log n\]for some constant $c_\alpha$ depending only on $\alpha$.



It is easy to show that, for every $0\leq \alpha\leq 1/2$,\[F(n,\alpha)\asymp_\alpha \log n.\]Note that when $\alpha=0$ this is just asking for a $2$-colouring of the edges of $K_n$ which contains no monochromatic clique of size $m$, and hence we recover the classical Ramsey numbers.

See also [161].

See also the entry in the graphs problem collection.


Back to the problem
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 563
erdosUrl: https://erdosproblems.com/563

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
- [Problem #161](https://www.erdosproblems.com/161)
- [Problem #562](https://www.erdosproblems.com/562)
- [Problem #564](https://www.erdosproblems.com/564)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Er90b]

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
