# Problem: Erdős #538

## Statement

### Plain Language
Let $r\geq 2$ and suppose that $A\subseteq\{1,\ldots,N\}$ is such that, for any $m$, there are at most $r$ solutions to $m=pa$ where $p$ is prime and $a\in A$. Give the best possible upper bound for\[\sum_{n\in A}\frac{1}{n}.\]



Erd\H{o}s observed that\[\sum_{n\in A}\frac{1}{n}\sum_{p\leq N}\frac{1}{p}\leq r\sum_{m\leq N^2}\frac{1}{m}\ll r\log N,\]and hence\[\sum_{n\in A}\frac{1}{n} \ll r\frac{\log N}{\log\log N}.\]See ...


### Formal Statement
$$
Let $r\geq 2$ and suppose that $A\subseteq\{1,\ldots,N\}$ is such that, for any $m$, there are at most $r$ solutions to $m=pa$ where $p$ is prime and $a\in A$. Give the best possible upper bound for\[\sum_{n\in A}\frac{1}{n}.\]



Erd\H{o}s observed that\[\sum_{n\in A}\frac{1}{n}\sum_{p\leq N}\frac{1}{p}\leq r\sum_{m\leq N^2}\frac{1}{m}\ll r\log N,\]and hence\[\sum_{n\in A}\frac{1}{n} \ll r\frac{\log N}{\log\log N}.\]See also [536] and [537].
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 538
erdosUrl: https://erdosproblems.com/538

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
- [Problem #536](https://www.erdosproblems.com/536)
- [Problem #537](https://www.erdosproblems.com/537)
- [Problem #539](https://www.erdosproblems.com/539)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Er73]

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
