# Problem: Erdős #409

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

How many iterations of $n\mapsto \phi(n)+1$ are needed before a prime is reached? Can infinitely many $n$ reach the same prime? What is the density of $n$ which reach any fixed prime?



A problem of Finucane. One can also ask similar questions about $n\mapsto \sigma(n)-1$: do iterates of this always reach a prime? If so, how soon? (It is easily seen that iterates of this cannot reach the same prime infinitely often, sinc...

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

How many iterations of $n\mapsto \phi(n)+1$ are needed before a prime is reached? Can infinitely many $n$ reach the same prime? What is the density of $n$ which reach any fixed prime?



A problem of Finucane. One can also ask similar questions about $n\mapsto \sigma(n)-1$: do iterates of this always reach a prime? If so, how soon? (It is easily seen that iterates of this cannot reach the same prime infinitely often, since they are non-decreasing.)

This problem is somewhat ambiguously phrased. Let $F(n)$ count the number of iterations of $n\mapsto \phi(n)+1$ before reaching a prime. The number of iterations required is A039651 in the OEIS.

Cambie notes in the comments that $F(n)=o(n)$ is trivial, and $F(n)=1$ infinitely often. Presumably the intended question is to find 'good' upper bounds for $F(n)$.

This is discussed in problem B41 of Guy's collection \cite{Gu04}.





References


[Gu04] Guy, Richard K., Unsolved problems in number theory. (2004), xviii+437.


Back to the problem
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 409
erdosUrl: https://erdosproblems.com/409

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
- [Problem #408](https://www.erdosproblems.com/408)
- [Problem #410](https://www.erdosproblems.com/410)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Gu04]

## OEIS Sequences

- [A039651](https://oeis.org/A039651)
- [A229487](https://oeis.org/A229487)
- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
