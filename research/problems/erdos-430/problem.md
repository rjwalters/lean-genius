# Problem: Erdős #430

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

Fix some integer $n$ and define a decreasing sequence in $[1,n)$ by $a_1=n-1$ and, for $k\geq 2$, letting $a_k$ be the greatest integer in $[1,a_{k-1})$ such that all of the prime factors of $a_k$ are $>n-a_k$.

Is it true that, for sufficiently large $n$, not all of this sequence can be prime?



Erd\H{o}s and Graham write 'preliminary calculations made by Selfridge indicate that this is the case but no proof is in sight...

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

Fix some integer $n$ and define a decreasing sequence in $[1,n)$ by $a_1=n-1$ and, for $k\geq 2$, letting $a_k$ be the greatest integer in $[1,a_{k-1})$ such that all of the prime factors of $a_k$ are $>n-a_k$.

Is it true that, for sufficiently large $n$, not all of this sequence can be prime?



Erd\H{o}s and Graham write 'preliminary calculations made by Selfridge indicate that this is the case but no proof is in sight'. For example if $n=8$ we have $a_1=7$ and $a_2=5$ and then must stop.

Sarosh Adenwalla has observed that this problem is equivalent to (the first part of) [385]. Indeed, assuming a positive answer to that, for all large $n$, there exists a composite $m<n$ such that all primes dividing $m$ are $>n-m$. It follows that such an $m$ is equal to some $a_i$ in the sequence defined for $[1,n)$, and $m$ is composite by assumption.


Back to the problem
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 430
erdosUrl: https://erdosproblems.com/430

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
- [Problem #385](https://www.erdosproblems.com/385)
- [Problem #429](https://www.erdosproblems.com/429)
- [Problem #431](https://www.erdosproblems.com/431)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [ErGr80]

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
