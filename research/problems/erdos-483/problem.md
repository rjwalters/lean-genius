# Problem: Erdős #483

## Statement

### Plain Language
Let $f(k)$ be the minimal $N$ such that if $\{1,\ldots,N\}$ is $k$-coloured then there is a monochromatic solution to $a+b=c$. Estimate $f(k)$. In particular, is it true that $f(k) 0$?



The values of $f(k)$ are known as Schur numbers. The best-known bounds for large $k$ are\[(380)^{k/5}-O(1)\leq f(k) \leq \lfloor(e-\tfrac{1}{24}) k!\rfloor-1.\]The lower bound is due to Ageron, Casteras, Pellerin, Portella, Rimmel, and T...


### Formal Statement
$$
Let $f(k)$ be the minimal $N$ such that if $\{1,\ldots,N\}$ is $k$-coloured then there is a monochromatic solution to $a+b=c$. Estimate $f(k)$. In particular, is it true that $f(k) < c^k$ for some constant $c>0$?



The values of $f(k)$ are known as Schur numbers. The best-known bounds for large $k$ are\[(380)^{k/5}-O(1)\leq f(k) \leq \lfloor(e-\tfrac{1}{24}) k!\rfloor-1.\]The lower bound is due to Ageron, Casteras, Pellerin, Portella, Rimmel, and Tomasik \cite{ACPPRT21} (improving previous bounds of Exoo \cite{Ex94} and Fredricksen and Sweet \cite{FrSw00}) and the upper bound is due to Whitehead \cite{Wh73}. Note that $380^{1/5}\approx 3.2806$.

The known values of $f$ are $f(1)=2$, $f(2)=5$, $f(3)=14$, $f(4)=45$, and $f(5)=161$ (see A030126). (The equality $f(5)=161$ was established by Heule \cite{He17}).

See also [183] (in particular a folklore observation gives $f(k)\leq R(3;k)-1$).
$$

## Classification

```yaml
tier: C
significance: 5
tractability: 3
erdosNumber: 483
erdosUrl: https://erdosproblems.com/483

tags:
  - erdos
```

**Significance**: 5/10
**Tractability**: 3/10

## Why This Matters

1. **Erdős Legacy** - Part of Paul Erdős's influential problem collection
2. **Mathematical significance** - open problem; long statement


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
- [Problem #183](https://www.erdosproblems.com/183)
- [Problem #482](https://www.erdosproblems.com/482)
- [Problem #484](https://www.erdosproblems.com/484)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)
- [Problem #20](https://www.erdosproblems.com/20)

## References

- [ACPPRT21]
- [Ex94]
- [FrSw00]
- [Wh73]
- [He17]

## OEIS Sequences

- [A030126](https://oeis.org/A030126)
- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
