# Problem: Erdős #261

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

Are there infinitely many $n$ such that there exists some $t\geq 2$ and distinct integers $a_1,\ldots,a_t\geq 1$ such that\[\frac{n}{2^n}=\sum_{1\leq k\leq t}\frac{a_k}{2^{a_k}}?\]Is this true for all $n$? Is there a rational $x$ such that\[x = \sum_{k=1}^\infty \frac{a_k}{2^{a_k}}\]has at least $2^{\aleph_0}$ solutions?





Related to [260].

In \cite{Er88c} Erd\H{o}s notes that Cusick had a simple proof that there do e...

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

Are there infinitely many $n$ such that there exists some $t\geq 2$ and distinct integers $a_1,\ldots,a_t\geq 1$ such that\[\frac{n}{2^n}=\sum_{1\leq k\leq t}\frac{a_k}{2^{a_k}}?\]Is this true for all $n$? Is there a rational $x$ such that\[x = \sum_{k=1}^\infty \frac{a_k}{2^{a_k}}\]has at least $2^{\aleph_0}$ solutions?





Related to [260].

In \cite{Er88c} Erd\H{o}s notes that Cusick had a simple proof that there do exist infinitely many such $n$. Erd\H{o}s does not record what this was, but a later paper by Borwein and Loring \cite{BoLo90} provides the following proof: for every positive integer $m$ and $n=2^{m+1}-m-2$ we have\[\frac{n}{2^n}=\sum_{n<k\leq n+m}\frac{k}{2^k}.\]Tengely, Ulas, and Zygadlo \cite{TUZ20} have verified that all $n\leq 10000$ have the required property.

In \cite{Er88c} Erd\H{o}s weakens the second question to asking for the existence of a rational $x$ which has two solutions.




References


[BoLo90] Borwein, Peter and Loring, Terry A., Some questions of {E}rd\H{o}s and {G}raham on numbers of the
form {$\sum g_n/2^{g_n}$}. Math. Comp. (1990), 377--394.

[Er88c] Erd\"{o}s, P., On the irrationality of certain series: problems and results. New advances in transcendence theory (Durham, 1986) (1988), 102-109.

[TUZ20] Tengely, Szabolcs and Ulas, Maciej and Zygad\l o, Jakub, On a {D}iophantine equation of {E}rd\H{o}s and {G}raham. J. Number Theory (2020), 445--459.


Back to the problem
$$

## Classification

```yaml
tier: C
significance: 5
tractability: 3
erdosNumber: 261
erdosUrl: https://erdosproblems.com/261

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
- [Problem #260](https://www.erdosproblems.com/260)
- [Problem #262](https://www.erdosproblems.com/262)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Er74b]
- [ErGr80]
- [Er88c]
- [BoLo90]
- [TUZ20]

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
