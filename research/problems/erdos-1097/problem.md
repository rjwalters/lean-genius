# Problem: Erdős #1097

## Statement

### Plain Language
Let $A$ be a set of $n$ integers. How many distinct $d$ can occur as the common difference of a three-term arithmetic progression in $A$? Are there always $O(n^{3/2})$ many such $d$?



A problem Erd\H{o}s posed in the 1989 problem session of Great Western Number Theory.

He states that Erd\H{o}s and Ruzsa gave an explicit construction which achieved $n^{1+c}$ for some $c>0$, and Erd\H{o}s and Spencer gave a probabilistic...


### Formal Statement
$$
Let $A$ be a set of $n$ integers. How many distinct $d$ can occur as the common difference of a three-term arithmetic progression in $A$? Are there always $O(n^{3/2})$ many such $d$?



A problem Erd\H{o}s posed in the 1989 problem session of Great Western Number Theory.

He states that Erd\H{o}s and Ruzsa gave an explicit construction which achieved $n^{1+c}$ for some $c>0$, and Erd\H{o}s and Spencer gave a probabilistic proof which achieved $n^{3/2}$, and speculated this may be the best possible.

In the comment section, Chan has noticed that this problem is exactly equivalent to a sums-differences question of Bourgain \cite{Bo99}, introduced as an arithmetic path towards the Kakeya conjecture: find the smallest $c\in [1,2]$ such that, for any finite sets of integers $A$ and $B$ and $G\subseteq A\times B$ we have\[\lvert A\overset{G}{-}B\rvert \ll \max(\lvert A\rvert,\lvert B\rvert, \lvert A\overset{G}{+}B\rvert)^c\](where, for example, $A\overset{G}{+}B$ denotes the set of $a+b$ with $(a,b)\in G$).

This is equivalent in the sense that the greatest exponent $c$ achievable for the main problem here is equal to the smallest constant achievable for the sums-differences question. The current best bounds known are thus\[1.77898\cdots \leq c \leq 11/6 \approx 1.833.\]The upper bound is due to Katz and Tao \cite{KaTa99}. The lower bound is due to Lemm \cite{Le15} (with a very small improvement found by AlphaEvolve \cite{GGTW25}).
$$

## Classification

```yaml
tier: C
significance: 5
tractability: 3
erdosNumber: 1097
erdosUrl: https://erdosproblems.com/1097

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
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #6](https://www.erdosproblems.com/6)
- [Problem #1096](https://www.erdosproblems.com/1096)
- [Problem #1098](https://www.erdosproblems.com/1098)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [GWNT89]
- [Bo99]
- [KaTa99]
- [Le15]
- [GGTW25]

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
