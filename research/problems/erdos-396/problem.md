# Problem: Erdős #396

## Statement

### Plain Language
Is it true that for every $k$ there exists $n$ such that\[\prod_{0\leq i\leq k}(n-i) \mid \binom{2n}{n}?\]



Erd\H{o}s and Graham write that $n+1$ always divides $\binom{2n}{n}$ (indeed $\frac{1}{n+1}\binom{2n}{n}$ is the $n$th Catalan number), but it is quite rare that $n$ divides $\binom{2n}{n}$.

Pomerance \cite{Po14} has shown that for any $k\geq 0$ there are infinitely many $n$ such that $n-k\mid\binom{2n}{n}$, alth...


### Formal Statement
$$
Is it true that for every $k$ there exists $n$ such that\[\prod_{0\leq i\leq k}(n-i) \mid \binom{2n}{n}?\]



Erd\H{o}s and Graham write that $n+1$ always divides $\binom{2n}{n}$ (indeed $\frac{1}{n+1}\binom{2n}{n}$ is the $n$th Catalan number), but it is quite rare that $n$ divides $\binom{2n}{n}$.

Pomerance \cite{Po14} has shown that for any $k\geq 0$ there are infinitely many $n$ such that $n-k\mid\binom{2n}{n}$, although the set of such $n$ has upper density $<1/3$. Pomerance also shows that the set of $n$ such that\[\prod_{1\leq i\leq k}(n+i)\mid \binom{2n}{n}\]has density $1$.

The smallest $n$ for each $k$ are listed as A375077 on the OEIS.
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 396
erdosUrl: https://erdosproblems.com/396

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
- [Problem #3](https://www.erdosproblems.com/3)
- [Problem #395](https://www.erdosproblems.com/395)
- [Problem #397](https://www.erdosproblems.com/397)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [ErGr80]
- [Po14]

## OEIS Sequences

- [A375077](https://oeis.org/A375077)
- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
