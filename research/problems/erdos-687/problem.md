# Problem: Erdős #687

## Statement

### Plain Language
Let $Y(x)$ be the maximal $y$ such that there exists a choice of congruence classes $a_p$ for all primes $p\leq x$ such that every integer in $[1,y]$ is congruent to at least one of the $a_p\pmod{p}$.

Give good estimates for $Y(x)$. In particular, can one prove that $Y(x)=o(x^2)$ or even $Y(x)\ll x^{1+o(1)}$?



This function (associated with Jacobsthal) is closely related to the problem of gaps between primes (see [4])....


### Formal Statement
$$
Let $Y(x)$ be the maximal $y$ such that there exists a choice of congruence classes $a_p$ for all primes $p\leq x$ such that every integer in $[1,y]$ is congruent to at least one of the $a_p\pmod{p}$.

Give good estimates for $Y(x)$. In particular, can one prove that $Y(x)=o(x^2)$ or even $Y(x)\ll x^{1+o(1)}$?



This function (associated with Jacobsthal) is closely related to the problem of gaps between primes (see [4]). The best known upper bound is due to Iwaniec \cite{Iw78},\[Y(x) \ll x^2.\]The best lower bound is due to Ford, Green, Konyagin, Maynard, and Tao \cite{FGKMT18},\[Y(x) \gg x\frac{\log x\log\log\log x}{\log\log x},\]improving on a previous bound of Rankin \cite{Ra38}.

Maier and Pomerance have conjectured that $Y(x)\ll x(\log x)^{2+o(1)}$.

In \cite{Er80} he writes 'It is not clear who first formulated this problem - probably many of us did it independently. I offer the maximum of \$1000 dollars and $1/2$ my total savings for clearing up of this problem.'

In \cite{Er80} Erd\H{o}s also asks about a weaker variant in which all except $o(y/\log y)$ of the integers in $[1,y]$ are congruent to at least one of the $a_p\pmod{p}$, and in particular asks if the answer is very different.

See also [688] and [689]. A more general Jacobsthal function is the focus of [970].
$$

## Classification

```yaml
tier: D
significance: 4
tractability: 1
erdosNumber: 687
erdosUrl: https://erdosproblems.com/687
prize: $1000
tags:
  - erdos
```

**Significance**: 4/10
**Tractability**: 1/10

## Why This Matters

1. **Erdős Legacy** - Part of Paul Erdős's influential problem collection
2. **Mathematical significance** - open problem; long statement; large prize (famous open problem)
3. **Prize** - $1000 offered for solution

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| --- | --- |

## Related Problems

- [Problem #2000](https://www.erdosproblems.com/2000)
- [Problem #83](https://www.erdosproblems.com/83)
- [Problem #888](https://www.erdosproblems.com/888)
- [Problem #1998](https://www.erdosproblems.com/1998)
- [Problem #4](https://www.erdosproblems.com/4)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #688](https://www.erdosproblems.com/688)
- [Problem #689](https://www.erdosproblems.com/689)
- [Problem #970](https://www.erdosproblems.com/970)
- [Problem #686](https://www.erdosproblems.com/686)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Er96b]
- [Iw78]
- [FGKMT18]
- [Ra38]
- [Er80]

## OEIS Sequences

- [A048670](https://oeis.org/A048670)
- [A058989](https://oeis.org/A058989)
- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
