# Problem: Erdős #700

## Statement

### Plain Language
Let\[f(n)=\min_{1n^{1/2}$?{/LI}
{LI} Is it true that, for every composite $n$,\[f(n) \ll_A \frac{n}{(\log n)^A}\]for every $A>0$?{/LI}
{/UL}



A problem of Erd\H{o}s and Szekeres. It is easy to see that $f(n)\leq n/P(n)$ for composite $n$, since if $j=p^k$ where $p^k\mid n$ and $p^{k+1}\nmid n$ then $\textrm{gcd}\left(n,\binom{n}{j}\right)=n/p^k$. This implies\[f(n) \leq (1+o(1))\frac{n}{\log n}.\]It is known that $f(n)=...


### Formal Statement
$$
Let\[f(n)=\min_{1<k\leq n/2}\textrm{gcd}\left(n,\binom{n}{k}\right).\]{UL}
{LI}Characterise those composite $n$ such that $f(n)=n/P(n)$, where $P(n)$ is the largest prime dividing $n$.{/LI}
{LI}Are there infinitely many composite $n$ such that $f(n)>n^{1/2}$?{/LI}
{LI} Is it true that, for every composite $n$,\[f(n) \ll_A \frac{n}{(\log n)^A}\]for every $A>0$?{/LI}
{/UL}



A problem of Erd\H{o}s and Szekeres. It is easy to see that $f(n)\leq n/P(n)$ for composite $n$, since if $j=p^k$ where $p^k\mid n$ and $p^{k+1}\nmid n$ then $\textrm{gcd}\left(n,\binom{n}{j}\right)=n/p^k$. This implies\[f(n) \leq (1+o(1))\frac{n}{\log n}.\]It is known that $f(n)=n/P(n)$ when $n$ is the product of two primes. Another example is $n=30$.

For the second problem, it is easy to see that for any $n$ we have $f(n)\geq p(n)$, where $p(n)$ is the smallest prime dividing $n$, and hence there are infinitely many $n$ (those $=p^2)$ such that $f(n)\geq n^{1/2}$.
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 700
erdosUrl: https://erdosproblems.com/700

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
- [Problem #699](https://www.erdosproblems.com/699)
- [Problem #701](https://www.erdosproblems.com/701)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [ErSz78]

## OEIS Sequences

- [A091963](https://oeis.org/A091963)
- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
