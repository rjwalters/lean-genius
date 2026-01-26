# Problem: Erdős #533

## Statement

### Plain Language
Let $\delta>0$. If $n$ is sufficiently large and $G$ is a graph on $n$ vertices with no $K_5$ and at least $\delta n^2$ edges then $G$ contains a set of $\gg_\delta n$ vertices containing no triangle.




A problem of Erd\H{o}s, Hajnal, Simonovits, S\'{o}s, and Szemer\'{e}di, who could prove this is true for $\delta>1/16$, and could further prove it for $\delta>0$ if we replace $K_5$ with $K_4$.

They further observed tha...


### Formal Statement
$$
Let $\delta>0$. If $n$ is sufficiently large and $G$ is a graph on $n$ vertices with no $K_5$ and at least $\delta n^2$ edges then $G$ contains a set of $\gg_\delta n$ vertices containing no triangle.




A problem of Erd\H{o}s, Hajnal, Simonovits, S\'{o}s, and Szemer\'{e}di, who could prove this is true for $\delta>1/16$, and could further prove it for $\delta>0$ if we replace $K_5$ with $K_4$.

They further observed that it fails for $\delta =1/4$ if we replace $K_5$ with $K_7$: by a construction of Erd\H{o}s and Rogers \cite{ErRo62} (see [620]) there exists some constant $c>0$ such that, for all large $n$, there is a graph on $n$ vertices which contains no $K_4$ and every set of at least $n^{1-c}$ vertices contains a triangle. If we take two vertex disjoint copies of this graph and add all edges between the two copies then this yields a graph on $2n$ vertices with $\geq n^2$ edges, which contains no $K_7$, yet every set of at least $2n^{1-c}$ vertices contains a triangle.


See also [579] and the entry in the graphs problem collection.
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 533
erdosUrl: https://erdosproblems.com/533

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
- [Problem #16](https://www.erdosproblems.com/16)
- [Problem #4](https://www.erdosproblems.com/4)
- [Problem #620](https://www.erdosproblems.com/620)
- [Problem #579](https://www.erdosproblems.com/579)
- [Problem #532](https://www.erdosproblems.com/532)
- [Problem #534](https://www.erdosproblems.com/534)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Er91]
- [EHSSS94]
- [ErRo62]

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
