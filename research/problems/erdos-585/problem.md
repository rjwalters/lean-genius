# Problem: Erdős #585

## Statement

### Plain Language
What is the maximum number of edges that a graph on $n$ vertices can have if it does not contain two edge-disjoint cycles with the same vertex set?



Pyber, R\"{o}dl, and Szemer\'{e}di \cite{PRS95} constructed such a graph with $\gg n\log\log n$ edges.

Chakraborti, Janzer, Methuku, and Montgomery \cite{CJMM24} have shown that such a graph can have at most $n(\log n)^{O(1)}$ many edges. Indeed, they prove that there exis...


### Formal Statement
$$
What is the maximum number of edges that a graph on $n$ vertices can have if it does not contain two edge-disjoint cycles with the same vertex set?



Pyber, R\"{o}dl, and Szemer\'{e}di \cite{PRS95} constructed such a graph with $\gg n\log\log n$ edges.

Chakraborti, Janzer, Methuku, and Montgomery \cite{CJMM24} have shown that such a graph can have at most $n(\log n)^{O(1)}$ many edges. Indeed, they prove that there exists a constant $C>0$ such that for any $k\geq 2$ there is a $c_k$ such that if a graph has $n$ vertices and at least $c_kn(\log n)^{C}$ many edges then it contains $k$ pairwise edge-disjoint cycles with the same vertex set.
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 585
erdosUrl: https://erdosproblems.com/585

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
- [Problem #584](https://www.erdosproblems.com/584)
- [Problem #586](https://www.erdosproblems.com/586)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Er76b]
- [PRS95]
- [CJMM24]

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
