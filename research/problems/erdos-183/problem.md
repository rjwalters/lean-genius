# Problem: Erdős #183

## Statement

### Plain Language
Let $R(3;k)$ be the minimal $n$ such that if the edges of $K_n$ are coloured with $k$ colours then there must exist a monochromatic triangle. Determine\[\lim_{k\to \infty}R(3;k)^{1/k}.\]



Erd\H{o}s offers \$100 for showing that this limit is finite. An easy pigeonhole argument shows that\[R(3;k)\leq 2+k(R(3;k-1)-1),\]from which $R(3;k)\leq \lceil e k!\rceil$ immediately follows. The best-known upper bounds are all of th...


### Formal Statement
$$
Let $R(3;k)$ be the minimal $n$ such that if the edges of $K_n$ are coloured with $k$ colours then there must exist a monochromatic triangle. Determine\[\lim_{k\to \infty}R(3;k)^{1/k}.\]



Erd\H{o}s offers \$100 for showing that this limit is finite. An easy pigeonhole argument shows that\[R(3;k)\leq 2+k(R(3;k-1)-1),\]from which $R(3;k)\leq \lceil e k!\rceil$ immediately follows. The best-known upper bounds are all of the form $ck!+O(1)$, and arise from this type of inductive relationship and computational bounds for $R(3;k)$ for small $k$. The best-known lower bound (coming from lower bounds for Schur numbers) is\[R(3,k)\geq (380)^{k/5}-O(1),\]due to Ageron, Casteras, Pellerin, Portella, Rimmel, and Tomasik \cite{ACPPRT21} (improving previous bounds of Exoo \cite{Ex94} and Fredricksen and Sweet \cite{FrSw00}). Note that $380^{1/5}\approx 3.2806$.

See also [483].

This problem is #21 in Ramsey Theory in the graphs problem collection.
$$

## Classification

```yaml
tier: C
significance: 5
tractability: 3
erdosNumber: 183
erdosUrl: https://erdosproblems.com/183
prize: $250
tags:
  - erdos
```

**Significance**: 5/10
**Tractability**: 3/10

## Why This Matters

1. **Erdős Legacy** - Part of Paul Erdős's influential problem collection
2. **Mathematical significance** - open problem; long statement
3. **Prize** - $250 offered for solution

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| --- | --- |

## Related Problems

- [Problem #2000](https://www.erdosproblems.com/2000)
- [Problem #83](https://www.erdosproblems.com/83)
- [Problem #888](https://www.erdosproblems.com/888)
- [Problem #1998](https://www.erdosproblems.com/1998)
- [Problem #5](https://www.erdosproblems.com/5)
- [Problem #483](https://www.erdosproblems.com/483)
- [Problem #21](https://www.erdosproblems.com/21)
- [Problem #182](https://www.erdosproblems.com/182)
- [Problem #184](https://www.erdosproblems.com/184)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Er61]
- [ACPPRT21]
- [Ex94]
- [FrSw00]

## OEIS Sequences

- [A003323](https://oeis.org/A003323)
- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
