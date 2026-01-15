# Problem: Erdős #960

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

Let $r,k\geq 2$ be fixed. Let $A\subset \mathbb{R}^2$ be a set of $n$ points with no $k$ points on a line. Determine the threshold $f_{r,k}(n)$ such that if there are at least $f_{r,k}(n)$ many ordinary lines (lines containing exactly two points) then there is a set $A'\subseteq A$ of $r$ points such that all $\binom{r}{2}$ many lines determined by $A'$ are ordinary.

Is it true that $f_{r,k}(n)=o(n^2)$, or perhaps even $...

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

Let $r,k\geq 2$ be fixed. Let $A\subset \mathbb{R}^2$ be a set of $n$ points with no $k$ points on a line. Determine the threshold $f_{r,k}(n)$ such that if there are at least $f_{r,k}(n)$ many ordinary lines (lines containing exactly two points) then there is a set $A'\subseteq A$ of $r$ points such that all $\binom{r}{2}$ many lines determined by $A'$ are ordinary.

Is it true that $f_{r,k}(n)=o(n^2)$, or perhaps even $\ll n$?



Tur\'{a}n's theorem implies\[f_{r,k}(n) \leq \left(1-\frac{1}{r-1}\right)\frac{n^2}{2}+1.\]See also [209].


Back to the problem
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 960
erdosUrl: https://erdosproblems.com/960

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
- [Problem #209](https://www.erdosproblems.com/209)
- [Problem #959](https://www.erdosproblems.com/959)
- [Problem #961](https://www.erdosproblems.com/961)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Er84]

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
