# Problem: Erdős #667

## Statement

### Plain Language
Let $p,q\geq 1$ be fixed integers. We define $H(n)=H(N;p,q)$ to be the largest $m$ such that any graph on $n$ vertices where every set of $p$ vertices spans at least $q$ edges must contain a complete graph on $m$ vertices.
Is\[c(p,q)=\liminf \frac{\log H(n)}{\log n}\]a strictly increasing function of $q$ for $1\leq q\leq \binom{p-1}{2}+1$?



A problem of Erd\H{o}s, Faudree, Rousseau, and Schelp.

When $q=1$ this correspo...


### Formal Statement
$$
Let $p,q\geq 1$ be fixed integers. We define $H(n)=H(N;p,q)$ to be the largest $m$ such that any graph on $n$ vertices where every set of $p$ vertices spans at least $q$ edges must contain a complete graph on $m$ vertices.
Is\[c(p,q)=\liminf \frac{\log H(n)}{\log n}\]a strictly increasing function of $q$ for $1\leq q\leq \binom{p-1}{2}+1$?



A problem of Erd\H{o}s, Faudree, Rousseau, and Schelp.

When $q=1$ this corresponds exactly to the classical Ramsey problem, and hence for example\[\frac{1}{p-1}\leq c(p,1) \leq \frac{2}{p+1}.\]It is easy to see that if $q=\binom{p-1}{2}+1$ then $c(p,q)=1$. Erd\H{o}s, Faudree, Rousseau, and Schelp have shown that $c(p,\binom{p-1}{2})\leq 1/2$.
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 667
erdosUrl: https://erdosproblems.com/667

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
- [Problem #666](https://www.erdosproblems.com/666)
- [Problem #668](https://www.erdosproblems.com/668)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Er97f]

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
