# Problem: Erdős #319

## Statement

### Plain Language
What is the size of the largest $A\subseteq \{1,\ldots,N\}$ such that there is a function $\delta:A\to \{-1,1\}$ such that\[\sum_{n\in A}\frac{\delta_n}{n}=0\]and\[\sum_{n\in A'}\frac{\delta_n}{n}\neq 0\]for all non-empty $A'\subsetneq A$?



Adenwalla has observed that a lower bound of\[\lvert A\rvert\geq (1-\tfrac{1}{e}+o(1))N\]follows from the main result of Croot \cite{Cr01}, which states that there exists some set of...


### Formal Statement
$$
What is the size of the largest $A\subseteq \{1,\ldots,N\}$ such that there is a function $\delta:A\to \{-1,1\}$ such that\[\sum_{n\in A}\frac{\delta_n}{n}=0\]and\[\sum_{n\in A'}\frac{\delta_n}{n}\neq 0\]for all non-empty $A'\subsetneq A$?



Adenwalla has observed that a lower bound of\[\lvert A\rvert\geq (1-\tfrac{1}{e}+o(1))N\]follows from the main result of Croot \cite{Cr01}, which states that there exists some set of integers $B\subset [(\frac{1}{e}-o(1))N,N]$ such that $\sum_{b\in B}\frac{1}{b}=1$. Since the sum of $\frac{1}{m}$ for $m\in [c_1N,c_2N]$ is asymptotic to $\log(c_2/c_1)$ we must have $\lvert B\rvert \geq (1-\tfrac{1}{e}+o(1))N$.

We may then let $A=B\cup\{1\}$ and choose $\delta(n)=-1$ for all $n\in B$ and $\delta(1)=1$.

This problem has been formalised in Lean as part of the Google DeepMind Formal Conjectures project.
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 319
erdosUrl: https://erdosproblems.com/319

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
- [Problem #318](https://www.erdosproblems.com/318)
- [Problem #320](https://www.erdosproblems.com/320)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [ErGr80]
- [Cr01]

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
