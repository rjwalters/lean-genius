# Problem: Erdős #102

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

Let $c>0$ and $h_c(n)$ be such that for any $n$ points in $\mathbb{R}^2$ such that there are $\geq cn^2$ lines each containing more than three points, there must be some line containing $h_c(n)$ many points. Estimate $h_c(n)$. Is it true that, for fixed $c>0$, we have $h_c(n)\to \infty$?



A problem of Erd\H{o}s and Purdy. It is not even known if $h_c(n)\geq 5$ (see [101]).

It is easy to see that $h_c(n) \ll_c n^{1/2}$,...

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

Let $c>0$ and $h_c(n)$ be such that for any $n$ points in $\mathbb{R}^2$ such that there are $\geq cn^2$ lines each containing more than three points, there must be some line containing $h_c(n)$ many points. Estimate $h_c(n)$. Is it true that, for fixed $c>0$, we have $h_c(n)\to \infty$?



A problem of Erd\H{o}s and Purdy. It is not even known if $h_c(n)\geq 5$ (see [101]).

It is easy to see that $h_c(n) \ll_c n^{1/2}$, and Erd\H{o}s at one point \cite{Er95} suggested that perhaps a similar lower bound $h_c(n)\gg_c n^{1/2}$ holds. Zach Hunter has pointed out that this is false, even replacing $>3$ points on each line with $>k$ points: consider the set of points in $\{1,\ldots,m\}^d$ where $n\approx m^d$. These intersect any line in $\ll_d n^{1/d}$ points, and have $\gg_d n^2$ many pairs of points each of which determine a line with at least $k$ points. This is a construction in $\mathbb{R}^d$, but a random projection into $\mathbb{R}^2$ preserves the relevant properties.

This construction shows that $h_c(n) \ll n^{1/\log(1/c)}$.




References


[Er95] Erd\H{o}s, Paul, Some of my favourite problems in number theory, combinatorics, and geometry. Resenhas (1995), 165-186.


Back to the problem
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 102
erdosUrl: https://erdosproblems.com/102

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
- [Problem #101](https://www.erdosproblems.com/101)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #103](https://www.erdosproblems.com/103)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Er92e]
- [Er95]
- [Er97c]

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
