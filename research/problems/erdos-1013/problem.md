# Problem: Erdős #1013

## Statement

### Plain Language
Let $h_3(k)$ be the minimal $n$ such that there exists a triangle-free graph on $n$ vertices with chromatic number $k$. Find an asymptotic for $h_3(k)$, and also prove\[\lim_{k\to \infty}\frac{h_3(k+1)}{h_3(k)}=1.\]



It is known that\[\frac{\log k}{\log\log k}k^2 \ll h_3(k) \ll (\log k)k^2.\]The lower bound is due to Graver and Yackel \cite{GrYa68}, the upper bound follows from Shearer's upper bound for $R(3,k)$ (see [1...


### Formal Statement
$$
Let $h_3(k)$ be the minimal $n$ such that there exists a triangle-free graph on $n$ vertices with chromatic number $k$. Find an asymptotic for $h_3(k)$, and also prove\[\lim_{k\to \infty}\frac{h_3(k+1)}{h_3(k)}=1.\]



It is known that\[\frac{\log k}{\log\log k}k^2 \ll h_3(k) \ll (\log k)k^2.\]The lower bound is due to Graver and Yackel \cite{GrYa68}, the upper bound follows from Shearer's upper bound for $R(3,k)$ (see [165]).

The function $h_r(k)$ for $r\geq 4$ is the subject of [920].
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 1013
erdosUrl: https://erdosproblems.com/1013

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
- [Problem #165](https://www.erdosproblems.com/165)
- [Problem #920](https://www.erdosproblems.com/920)
- [Problem #1012](https://www.erdosproblems.com/1012)
- [Problem #1014](https://www.erdosproblems.com/1014)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Er71]
- [GrYa68]

## OEIS Sequences

- [A292528](https://oeis.org/A292528)
- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
