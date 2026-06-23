# Problem: Erdős #935

## Statement

### Plain Language
For any integer $n=\prod p^{k_p}$ let $Q_2(n)$ be the powerful part of $n$, so that\[Q_2(n) = \prod_{\substack{p\\ k_p\geq 2}}p^{k_p}.\]Is it true that, for every $\epsilon>0$ and $\ell\geq 1$, if $n$ is sufficiently large then\[Q_2(n(n+1)\cdots(n+\ell))2$, only keeping those prime powers with exponent $\geq r$.


### Formal Statement
$$
For any integer $n=\prod p^{k_p}$ let $Q_2(n)$ be the powerful part of $n$, so that\[Q_2(n) = \prod_{\substack{p\\ k_p\geq 2}}p^{k_p}.\]Is it true that, for every $\epsilon>0$ and $\ell\geq 1$, if $n$ is sufficiently large then\[Q_2(n(n+1)\cdots(n+\ell))<n^{2+\epsilon}?\]If $\ell\geq 2$ then is\[\limsup_{n\to \infty}\frac{Q_2(n(n+1)\cdots(n+\ell))}{n^2}\]infinite?

If $\ell\geq 2$ then is\[\lim_{n\to \infty}\frac{Q_2(n(n+1)\cdots(n+\ell))}{n^{\ell+1}}=0?\]



Erd\H{o}s \cite{Er76d} writes that if this is true then it 'seems very difficult to prove'.

A result of Mahler implies, for every $\ell\geq 1$,\[\limsup_{n\to \infty}\frac{Q_2(n(n+1)\cdots(n+\ell))}{n^2}\geq 1.\]All these questions can be asked replacing $Q_2$ by $Q_r$ for $r>2$, only keeping those prime powers with exponent $\geq r$.
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 935
erdosUrl: https://erdosproblems.com/935

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
- [Problem #934](https://www.erdosproblems.com/934)
- [Problem #936](https://www.erdosproblems.com/936)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Er76d]

## OEIS Sequences

- [A057521](https://oeis.org/A057521)
- [A389244](https://oeis.org/A389244)
- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
