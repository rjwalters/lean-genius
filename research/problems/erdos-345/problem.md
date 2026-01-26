# Problem: Erdős #345

## Statement

### Plain Language
Let $A\subseteq \mathbb{N}$ be a complete sequence, and define the threshold of completeness $T(A)$ to be the least integer $m$ such that all $n\geq m$ are in\[P(A) = \left\{\sum_{n\in B}n : B\subseteq A\textrm{ finite }\right\}\](the existence of $T(A)$ is guaranteed by completeness).

Is it true that there are infinitely many $k$ such that $T(n^k)>T(n^{k+1})$?



Erd\H{o}s and Graham \cite{ErGr80} remark that very littl...


### Formal Statement
$$
Let $A\subseteq \mathbb{N}$ be a complete sequence, and define the threshold of completeness $T(A)$ to be the least integer $m$ such that all $n\geq m$ are in\[P(A) = \left\{\sum_{n\in B}n : B\subseteq A\textrm{ finite }\right\}\](the existence of $T(A)$ is guaranteed by completeness).

Is it true that there are infinitely many $k$ such that $T(n^k)>T(n^{k+1})$?



Erd\H{o}s and Graham \cite{ErGr80} remark that very little is known about $T(A)$ in general. It is known that\[T(n)=1, T(n^2)=128, T(n^3)=12758,\]\[T(n^4)=5134240,\textrm{ and }T(n^5)=67898771.\]Erd\H{o}s and Graham remark that a good candidate for the $n$ in the question are $k=2^t$ for large $t$, perhaps even $t=3$, because of the highly restricted values of $n^{2^t}$ modulo $2^{t+1}$.
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 345
erdosUrl: https://erdosproblems.com/345

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
- [Problem #344](https://www.erdosproblems.com/344)
- [Problem #346](https://www.erdosproblems.com/346)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [ErGr80]

## OEIS Sequences

- [A001661](https://oeis.org/A001661)
- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
