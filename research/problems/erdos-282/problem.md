# Problem: Erdős #282

## Statement

### Plain Language
Let $A\subseteq \mathbb{N}$ be an infinite set and consider the following greedy algorithm for a rational $x\in (0,1)$: choose the minimal $n\in A$ such that $n\geq 1/x$ and repeat with $x$ replaced by $x-\frac{1}{n}$. If this terminates after finitely many steps then this produces a representation of $x$ as the sum of distinct unit fractions with denominators from $A$.

Does this process always terminate if $x$ has odd d...


### Formal Statement
$$
Let $A\subseteq \mathbb{N}$ be an infinite set and consider the following greedy algorithm for a rational $x\in (0,1)$: choose the minimal $n\in A$ such that $n\geq 1/x$ and repeat with $x$ replaced by $x-\frac{1}{n}$. If this terminates after finitely many steps then this produces a representation of $x$ as the sum of distinct unit fractions with denominators from $A$.

Does this process always terminate if $x$ has odd denominator and $A$ is the set of odd numbers? More generally, for which pairs $x$ and $A$ does this process terminate?



In 1202 Fibonacci observed that this process terminates for any $x$ when $A=\mathbb{N}$. The problem when $A$ is the set of odd numbers is due to Stein.

Graham \cite{Gr64b} has shown that $\frac{m}{n}$ is the sum of distinct unit fractions with denominators $\equiv a\pmod{d}$ if and only if\[\left(\frac{n}{(n,(a,d))},\frac{d}{(a,d)}\right)=1.\]Does the greedy algorithm always terminate in such cases?

Graham \cite{Gr64c} has also shown that $x$ is the sum of distinct unit fractions with square denominators if and only if $x\in [0,\pi^2/6-1)\cup [1,\pi^2/6)$. Does the greedy algorithm for this always terminate? Erd\H{o}s and Graham believe not - indeed, perhaps it fails to terminate almost always.

See also [206].
$$

## Classification

```yaml
tier: C
significance: 5
tractability: 3
erdosNumber: 282
erdosUrl: https://erdosproblems.com/282

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
- [Problem #6](https://www.erdosproblems.com/6)
- [Problem #206](https://www.erdosproblems.com/206)
- [Problem #281](https://www.erdosproblems.com/281)
- [Problem #283](https://www.erdosproblems.com/283)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Gr64b]
- [Gr64c]

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
