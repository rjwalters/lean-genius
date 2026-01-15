# Problem: Erdős #950

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

Let\[f(n) = \sum_{p0$ such that there are $\gg n^c/\log n$ many primes in $[n,n+n^c]$ implies that $\liminf f(n)>0$.

Erd\H{o}s writes that a 'weaker conjecture which is perhaps not quite inaccessible' is that, for every $\epsilon>0$, if $x$ is sufficiently large there exists $y0$ then $f(n)\ll \log\log\log n$.

The study of $f(p)$ is even harder, and Erd\H{o}s could not prove that\[\sum_{p<x}f(p)^2\sim \pi(x).\]


Back t...

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

Let\[f(n) = \sum_{p<n}\frac{1}{n-p}.\]Is it true that\[\liminf f(n)=1\]and\[\limsup f(n)=\infty?\]Is it true that $f(n)=o(\log\log n)$ for all $n$?



This function was considered by de Bruijn, Erd\H{o}s, and Tur\'{a}n, who showed that\[\sum_{n<x}f(n)\sim \sum_{n<x}f(n)^2\sim x.\]The existence of some $c>0$ such that there are $\gg n^c/\log n$ many primes in $[n,n+n^c]$ implies that $\liminf f(n)>0$.

Erd\H{o}s writes that a 'weaker conjecture which is perhaps not quite inaccessible' is that, for every $\epsilon>0$, if $x$ is sufficiently large there exists $y<x$ such that\[\pi(x)< \pi(y)+\epsilon \pi(x-y).\](Compare this to [855].) He notes that if\[\pi(x)< \pi(y)+O\left(\frac{x-y}{\log x}\right)\]for all $y<x-(\log x)^C$ for some constant $C>0$ then $f(n)\ll \log\log\log n$.

The study of $f(p)$ is even harder, and Erd\H{o}s could not prove that\[\sum_{p<x}f(p)^2\sim \pi(x).\]


Back to the problem
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 950
erdosUrl: https://erdosproblems.com/950

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
- [Problem #855](https://www.erdosproblems.com/855)
- [Problem #949](https://www.erdosproblems.com/949)
- [Problem #951](https://www.erdosproblems.com/951)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Er77c]

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
