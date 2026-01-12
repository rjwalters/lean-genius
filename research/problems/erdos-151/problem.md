# Problem: Erdős #151

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

For a graph $G$ let $\tau(G)$ denote the minimal number of vertices that include at least one from each maximal clique of $G$ on at least two vertices (sometimes called the clique transversal number).

Let $H(n)$ be maximal such that every triangle-free graph on $n$ vertices contains an independent set on $H(n)$ vertices.

If $G$ is a graph on $n$ vertices then is\[\tau(G)\leq n-H(n)?\]



It is easy to see that $\tau(G) ...

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

For a graph $G$ let $\tau(G)$ denote the minimal number of vertices that include at least one from each maximal clique of $G$ on at least two vertices (sometimes called the clique transversal number).

Let $H(n)$ be maximal such that every triangle-free graph on $n$ vertices contains an independent set on $H(n)$ vertices.

If $G$ is a graph on $n$ vertices then is\[\tau(G)\leq n-H(n)?\]



It is easy to see that $\tau(G) \leq n-\sqrt{n}$. Note also that if $G$ is triangle-free then trivially $\tau(G)\leq n-H(n)$.

This is listed in \cite{Er88} as a problem of Erd\H{o}s and Gallai, who were unable to make progress even assuming $G$ is $K_4$-free. There Erd\H{o}s remarked that this conjecture is 'perhaps completely wrongheaded'.

It later appeared as Problem 1 in \cite{EGT92}.

The general behaviour of $\tau(G)$ is the subject of [610].




References


[EGT92] Erd\H{o}s, Paul and Gallai, Tibor and Tuza, Zsolt, Covering the cliques of a graph with vertices. Discrete Math. (1992), 279-289.

[Er88] Erd\H{o}s, P, Problems and results in combinatorial analysis and graph theory. Discrete Math. (1988), 81-92.


Back to the problem
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 151
erdosUrl: https://erdosproblems.com/151

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
- [Problem #610](https://www.erdosproblems.com/610)
- [Problem #150](https://www.erdosproblems.com/150)
- [Problem #152](https://www.erdosproblems.com/152)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Er88]
- [EGT92]

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
