# Problem: Erdős #959

## Statement

### Plain Language
Let $A\subset \mathbb{R}^2$ be a set of size $n$ and let $\{d_1,\ldots,d_k\}$ be the set of distinct distances determined by $A$. Let $f(d)$ be the number of times the distance $d$ is determined, and suppose the $d_i$ are ordered such that\[f(d_1)\geq f(d_2)\geq \cdots \geq f(d_k).\]Estimate\[\max (f(d_1)-f(d_2)),\]where the maximum is taken over all $A$ of size $n$.



More generally, one can ask about\[\max (f(d_r)-f(d_...


### Formal Statement
$$
Let $A\subset \mathbb{R}^2$ be a set of size $n$ and let $\{d_1,\ldots,d_k\}$ be the set of distinct distances determined by $A$. Let $f(d)$ be the number of times the distance $d$ is determined, and suppose the $d_i$ are ordered such that\[f(d_1)\geq f(d_2)\geq \cdots \geq f(d_k).\]Estimate\[\max (f(d_1)-f(d_2)),\]where the maximum is taken over all $A$ of size $n$.



More generally, one can ask about\[\max (f(d_r)-f(d_{r+1})).\]Clemen, Dumitrescu, and Liu \cite{CDL25}, have shown that\[\max (f(d_1)-f(d_2))\gg n\log n.\]More generally, for any $1\leq k\leq \log n$, there exists a set $A$ of $n$ points such that\[f(d_r)-f(d_{r+1})\gg \frac{n\log n}{r}.\]They conjecture that $n\log n$ can be improved to $n^{1+c/\log\log n}$ for some constant $c>0$.
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 959
erdosUrl: https://erdosproblems.com/959

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
- [Problem #958](https://www.erdosproblems.com/958)
- [Problem #960](https://www.erdosproblems.com/960)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Er84d]
- [CDL25]

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
