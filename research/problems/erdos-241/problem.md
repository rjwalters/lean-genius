# Problem: Erdős #241

## Statement

### Plain Language
Let $f(N)$ be the maximum size of $A\subseteq \{1,\ldots,N\}$ such that the sums $a+b+c$ with $a,b,c\in A$ are all distinct (aside from the trivial coincidences). Is it true that\[ f(N)\sim N^{1/3}?\]



Originally asked to Erd\H{o}s by Bose. Bose and Chowla \cite{BoCh62} provided a construction proving one half of this, namely\[(1+o(1))N^{1/3}\leq f(N).\]The best upper bound known to date is due to Green \cite{Gr01},\[f(...


### Formal Statement
$$
Let $f(N)$ be the maximum size of $A\subseteq \{1,\ldots,N\}$ such that the sums $a+b+c$ with $a,b,c\in A$ are all distinct (aside from the trivial coincidences). Is it true that\[ f(N)\sim N^{1/3}?\]



Originally asked to Erd\H{o}s by Bose. Bose and Chowla \cite{BoCh62} provided a construction proving one half of this, namely\[(1+o(1))N^{1/3}\leq f(N).\]The best upper bound known to date is due to Green \cite{Gr01},\[f(N) \leq ((7/2)^{1/3}+o(1))N^{1/3}\](note that $(7/2)^{1/3}\approx 1.519$).

More generally, Bose and Chowla conjectured that the maximum size of $A\subseteq \{1,\ldots,N\}$ with all $r$-fold sums distinct (aside from the trivial coincidences) then\[\lvert A\rvert \sim N^{1/r}.\]This is known only for $r=2$ (see [30]).

This is discussed in problem C11 of Guy's collection \cite{Gu04}.
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 241
erdosUrl: https://erdosproblems.com/241
prize: $100
tags:
  - erdos
```

**Significance**: 6/10
**Tractability**: 4/10

## Why This Matters

1. **Erdős Legacy** - Part of Paul Erdős's influential problem collection
2. **Mathematical significance** - open problem
3. **Prize** - $100 offered for solution

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| --- | --- |

## Related Problems

- [Problem #2000](https://www.erdosproblems.com/2000)
- [Problem #83](https://www.erdosproblems.com/83)
- [Problem #888](https://www.erdosproblems.com/888)
- [Problem #1998](https://www.erdosproblems.com/1998)
- [Problem #3](https://www.erdosproblems.com/3)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #30](https://www.erdosproblems.com/30)
- [Problem #240](https://www.erdosproblems.com/240)
- [Problem #242](https://www.erdosproblems.com/242)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Er61]
- [Er69]
- [Er70b]
- [Er70c]
- [Er73]
- [Er77c]
- [ErGr80]
- [BoCh62]
- [Gr01]
- [Gu04]

## OEIS Sequences

- [A387704](https://oeis.org/A387704)
- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
