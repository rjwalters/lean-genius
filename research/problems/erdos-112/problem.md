# Problem: Erdős #112

## Statement

### Plain Language
Let $k=k(n,m)$ be minimal such that any directed graph on $k$ vertices must contain either an independent set of size $n$ or a transitive tournament of size $m$. Determine $k(n,m)$.



A problem of Erd\H{o}s and Rado \cite{ErRa67}, who showed $k(n,m) \ll_m n^{m-1}$, or more precisely,\[k(n,m) \leq \frac{2^{m-1}(n-1)^m+n-2}{2n-3}.\]Larson and Mitchell \cite{LaMi97} improved the dependence on $m$, establishing in particular...


### Formal Statement
$$
Let $k=k(n,m)$ be minimal such that any directed graph on $k$ vertices must contain either an independent set of size $n$ or a transitive tournament of size $m$. Determine $k(n,m)$.



A problem of Erd\H{o}s and Rado \cite{ErRa67}, who showed $k(n,m) \ll_m n^{m-1}$, or more precisely,\[k(n,m) \leq \frac{2^{m-1}(n-1)^m+n-2}{2n-3}.\]Larson and Mitchell \cite{LaMi97} improved the dependence on $m$, establishing in particular that $k(n,3)\leq n^{2}$. Zach Hunter has observed that\[R(n,m) \leq k(n,m)\leq R(n,m,m),\]which in particular proves the upper bound $k(n,m)\leq 3^{n+2m}$.


See also the entry in the graphs problem collection - on this site the problem replaces transitive tournament with directed path, but Zach Hunter and Raphael Steiner have a simple argument that proves, for this alternative definition, that $k(n,m)=(n-1)(m-1)$.
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 112
erdosUrl: https://erdosproblems.com/112

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
- [Problem #111](https://www.erdosproblems.com/111)
- [Problem #113](https://www.erdosproblems.com/113)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [ErRa67]
- [LaMi97]

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
