# Problem: Erdős #82

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

Let $F(n)$ be maximal such that every graph on $n$ vertices contains a regular induced subgraph on at least $F(n)$ vertices. Prove that $F(n)/\log n\to \infty$.



Conjectured by Erd\H{o}s, Fajtlowicz, and Stanton. It is known that $F(5)=3$ and $F(7)=4$.

Ramsey's theorem implies that $F(n)\gg \log n$. Bollob\'{a}s observed that $F(n)\ll n^{1/2+o(1)}$. Alon, Krivelevich, and Sudakov \cite{AKS07} have improved this to $n^{...

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

Let $F(n)$ be maximal such that every graph on $n$ vertices contains a regular induced subgraph on at least $F(n)$ vertices. Prove that $F(n)/\log n\to \infty$.



Conjectured by Erd\H{o}s, Fajtlowicz, and Stanton. It is known that $F(5)=3$ and $F(7)=4$.

Ramsey's theorem implies that $F(n)\gg \log n$. Bollob\'{a}s observed that $F(n)\ll n^{1/2+o(1)}$. Alon, Krivelevich, and Sudakov \cite{AKS07} have improved this to $n^{1/2}(\log n)^{O(1)}$.

In \cite{Er93} Erd\H{o}s asks whether, if $t(n)$ is the largest trivial (either empty or complete) subgraph which a graph on $n$ vertices must contain (so that $t(n) \gg \log n$ by Ramsey's theorem), then is it true that\[F(n)-t(n)\to \infty?\]Equivalently, and in analogue with the definition of Ramsey numbers, one can define $G(n)$ to be the minimal $m$ such that every graph on $m$ vertices contains a regular induced subgraph on at least $n$ vertices. This problem can be rephrased as asking whether $G(n) \leq 2^{o(n)}$.

Fajtlowicz, McColgan, Reid, and Staton \cite{FMRS95} showed that $G(1)=1$, $G(2)=2$, $G(3)=5$, $G(4)=7$, and $G(5)\geq 12$. Boris Alexeev and Brendan McKay (see the comments and this site) have computed $G(5)=17$, $G(6)\geq 21$, and $G(7)\geq 29$.

See also [1031] for another question regarding induced regular subgraphs.




References


[AKS07] Alon, N. and Krivelevich, M. and Sudakov, B., Large nearly regular induced subgraphs. arXiv:0710.2106 (2007).

[Er93] Erd\H{o}s, Paul, Some of my favorite solved and unsolved problems in graph
theory. Quaestiones Math. (1993), 333-350.

[FMRS95] No reference found.



Back to the problem
$$

## Classification

```yaml
tier: C
significance: 5
tractability: 3
erdosNumber: 82
erdosUrl: https://erdosproblems.com/82

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
- [Problem #1031](https://www.erdosproblems.com/1031)
- [Problem #81](https://www.erdosproblems.com/81)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Er95]
- [Er97d]
- [AKS07]
- [Er93]
- [FMRS95]

## OEIS Sequences

- [A120414](https://oeis.org/A120414)
- [A390256](https://oeis.org/A390256)
- [A390257](https://oeis.org/A390257)
- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
