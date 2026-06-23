# Problem: Erdős #1016

## Statement

### Plain Language
Let $h(n)$ be minimal such that there is a graph on $n$ vertices with $n+h(n)$ edges which contains a cycle on $k$ vertices, for all $3\leq k\leq n$. Estimate $h(n)$. In particular, is it true that\[h(n) \geq \log_2n+\log_*n-O(1),\]where $\log_*n$ is the iterated logarithmic function?



Such graphs are called pancyclic. A problem of Bondy \cite{Bo71}, who claimed a proof (without details) of\[\log_2(n-1)-1\leq h(n) \leq ...


### Formal Statement
$$
Let $h(n)$ be minimal such that there is a graph on $n$ vertices with $n+h(n)$ edges which contains a cycle on $k$ vertices, for all $3\leq k\leq n$. Estimate $h(n)$. In particular, is it true that\[h(n) \geq \log_2n+\log_*n-O(1),\]where $\log_*n$ is the iterated logarithmic function?



Such graphs are called pancyclic. A problem of Bondy \cite{Bo71}, who claimed a proof (without details) of\[\log_2(n-1)-1\leq h(n) \leq \log_2n+\log_*n+O(1).\]Erd\H{o}s \cite{Er71} believed the upper bound is closer to the truth, but could not even prove $h(n)-\log_2n\to \infty$.

A proof of the above lower bound is provided by Griffin \cite{Gr13}. The first published proof of the upper bound appears to be in Chapter 4.5 of George, Khodkar, and Wallis \cite{GKW16}.
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 1016
erdosUrl: https://erdosproblems.com/1016

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
- [Problem #1015](https://www.erdosproblems.com/1015)
- [Problem #1017](https://www.erdosproblems.com/1017)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Er71]
- [Bo71]
- [Gr13]
- [GKW16]

## OEIS Sequences

- [A105206](https://oeis.org/A105206)
- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
