# Problem: Erdős #889

## Statement

### Plain Language
For $k\geq 0$ and $n\geq 1$ let $v(n,k)$ count the prime factors of $n+k$ which do not divide $n+i$ for $0\leq ik$.

Is it true that\[v_0(n)=\max_{k\geq 0}v(n,k)\to \infty\]as $n\to \infty$?



A question of Erd\H{o}s and Selfridge \cite{ErSe67}, who could only show that $v_0(n)\geq 2$ for $n\geq 17$. More generally, they conjecture that\[v_l(n)=\max_{k\geq l}v(n,k)\to \infty\]as $n\to \infty$, for every fixed $l$, but co...


### Formal Statement
$$
For $k\geq 0$ and $n\geq 1$ let $v(n,k)$ count the prime factors of $n+k$ which do not divide $n+i$ for $0\leq i<k$. Equivalently, $v(n,k)$ counts the number of prime factors of $n+k$ which are $>k$.

Is it true that\[v_0(n)=\max_{k\geq 0}v(n,k)\to \infty\]as $n\to \infty$?



A question of Erd\H{o}s and Selfridge \cite{ErSe67}, who could only show that $v_0(n)\geq 2$ for $n\geq 17$. More generally, they conjecture that\[v_l(n)=\max_{k\geq l}v(n,k)\to \infty\]as $n\to \infty$, for every fixed $l$, but could not even prove that $v_1(n)\geq 2$ for all large $n$.

This is problem B27 of Guy's collection \cite{Gu04}.
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 889
erdosUrl: https://erdosproblems.com/889

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
- [Problem #890](https://www.erdosproblems.com/890)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [ErSe67]
- [Gu04]

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
