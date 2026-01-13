# Problem: Erdős #369

## Statement

### Plain Language
Forum
Favourites
Tags
More
 Go
 Go
Dual View
Random Solved
Random Open

Let $\epsilon>0$ and $k\geq 2$. Is it true that, for all sufficiently large $n$, there is a sequence of $k$ consecutive integers in $\{1,\ldots,n\}$ all of which are $n^\epsilon$-smooth?



Erd\H{o}s and Graham state that this is open even for $k=2$ and 'the answer should be affirmative but the problem seems very hard'.

Unfortunately the problem is trivially true as written (simply taking $\{1,\ldots,k\}$ and $n>k^{1/\ep...

### Formal Statement
$$
Forum
Favourites
Tags
More
 Go
 Go
Dual View
Random Solved
Random Open

Let $\epsilon>0$ and $k\geq 2$. Is it true that, for all sufficiently large $n$, there is a sequence of $k$ consecutive integers in $\{1,\ldots,n\}$ all of which are $n^\epsilon$-smooth?



Erd\H{o}s and Graham state that this is open even for $k=2$ and 'the answer should be affirmative but the problem seems very hard'.

Unfortunately the problem is trivially true as written (simply taking $\{1,\ldots,k\}$ and $n>k^{1/\epsilon}$). There are (at least) two possible variants which are non-trivial, and it is not clear which Erd\H{o}s and Graham meant. Let $P$ be the sequence of $k$ consecutive integers sought for. The potential strengthenings which make this non-trivial are:
{UL}
{LI}Each $m\in P$ must be $m^\epsilon$-smooth. If this is the problem then the answer is yes, which follows from a result of Balog and Wooley \cite{BaWo98}: for any $\epsilon>0$ and $k\geq 2$ there exist infinitely many $m$ such that $m+1,\ldots,m+k$ are all $m^\epsilon$-smooth.{/LI}
{LI}Each $m\in P$ must be in $[n/2,n]$ (say). In this case a positive answer also follows from the result of Balog and Wooley \cite{BaWo98} for infinitely many $n$, but the case of all sufficiently large $n$ is open.{/LI}
{/UL}

See also [370] and [928].




References


[BaWo98] Balog, Antal and Wooley, Trevor D., On strings of consecutive integers with no large prime factors. J. Austral. Math. Soc. Ser. A (1998), 266-276.


Back to the problem
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 369
erdosUrl: https://erdosproblems.com/369

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
- [Problem #370](https://www.erdosproblems.com/370)
- [Problem #928](https://www.erdosproblems.com/928)
- [Problem #368](https://www.erdosproblems.com/368)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [BaWo98]

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
