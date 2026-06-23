# Problem: Erdős #488

## Statement

### Plain Language
Let $A$ be a finite set and\[B=\{ n \geq 1 : a\mid n\textrm{ for some }a\in A\}.\]Is it true that, for every $m>n\geq \max(A)$,\[\frac{\lvert B\cap [1,m]\rvert }{m}< 2\frac{\lvert B\cap [1,n]\rvert}{n}?\]



The constant $2$ would be the best possible here, as witnessed by taking $A=\{a\}$, $n=2a-1$, and $m=2a$.

This problem is also discussed in problem E5 of Guy's collection \cite{Gu04}.

In \cite{Er61} this problem is ...


### Formal Statement
$$
Let $A$ be a finite set and\[B=\{ n \geq 1 : a\mid n\textrm{ for some }a\in A\}.\]Is it true that, for every $m>n\geq \max(A)$,\[\frac{\lvert B\cap [1,m]\rvert }{m}< 2\frac{\lvert B\cap [1,n]\rvert}{n}?\]



The constant $2$ would be the best possible here, as witnessed by taking $A=\{a\}$, $n=2a-1$, and $m=2a$.

This problem is also discussed in problem E5 of Guy's collection \cite{Gu04}.

In \cite{Er61} this problem is as stated above, but with $a\mid n$ in the definition of $B$ replaced by $a\nmid n$. This is most likely a typo (especially since the problem is also given as stated above in \cite{Er66}). There have been several counterexamples given for this alternate problem. Cambie has observed that, if $A$ is the set of primes bounded above by $n$, and $m=2n$, then\[\frac{\lvert B\cap [1,m]\rvert }{m}=\frac{\pi(2n)-\pi(n)+1}{2n}\sim \frac{1}{2\log n}\]while\[\frac{\lvert B\cap [1,n]\rvert}{n}=\frac{1}{n}.\]Further concrete counterexamples, found by Alexeev and Aristotle, are given in the comments section.
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 488
erdosUrl: https://erdosproblems.com/488

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
- [Problem #487](https://www.erdosproblems.com/487)
- [Problem #489](https://www.erdosproblems.com/489)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Gu04]
- [Er61]
- [Er66]

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
