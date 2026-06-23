# Problem: Erdős #358

## Statement

### Plain Language
Let $A=\{a_1<\cdots\}$ be an infinite sequence of integers. Let $f(n)$ count the number of solutions to\[n=\sum_{u\leq i\leq v}a_i.\]Is there such an $A$ for which $f(n)\to \infty$ as $n\to \infty$? Or even where $f(n)\geq 2$ for all large $n$?





When $a_n=n$ the function $f(n)$ counts the number of odd divisors of $n$.

In modern language, this asks for the existence of a convex set $A$ such that $1_A\circ 1_A(n)\to \...


### Formal Statement
$$
Let $A=\{a_1<\cdots\}$ be an infinite sequence of integers. Let $f(n)$ count the number of solutions to\[n=\sum_{u\leq i\leq v}a_i.\]Is there such an $A$ for which $f(n)\to \infty$ as $n\to \infty$? Or even where $f(n)\geq 2$ for all large $n$?





When $a_n=n$ the function $f(n)$ counts the number of odd divisors of $n$.

In modern language, this asks for the existence of a convex set $A$ such that $1_A\circ 1_A(n)\to \infty$ as $n\to \infty$.

Erd\H{o}s and Moser \cite{Mo63} considered the case when $A$ is the set of primes, and conjectured that the $\limsup$ of the number of such representations in this case is infinite. They could not even prove that the upper density of the set of integers representable in this form is positive.

In \cite{ErGr80} they further asked whether $f(n)\geq 1$ for all large $n$ is possible, but Egami observed the answer to this is trivially yes, taking $a_n=n$. Perhaps they intended to restrict $f(n)$ to only count those representatives as the sum of at least two consecutive terms. (It is a classical fact that $n$ can be expressed as a sum of at least two consecutive positive integers if and only if $n\neq 2^k$.)

In \cite{Er77c} Erd\H{o}s writes 'This problem can perhaps be rightly criticized as being artificial and in the backwater of Mathematics but it seems very strange and attractive to me'.

Weisenberg observes that the finite analogue of this problem, asking how many integers up to some $x$ can be written as the sum of consecutive elements, is very similar to [356].

This is reported in problem C2 of Guy's collection \cite{Gu04}.
$$

## Classification

```yaml
tier: C
significance: 5
tractability: 3
erdosNumber: 358
erdosUrl: https://erdosproblems.com/358

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
- [Problem #356](https://www.erdosproblems.com/356)
- [Problem #357](https://www.erdosproblems.com/357)
- [Problem #359](https://www.erdosproblems.com/359)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Er77c]
- [Mo63]
- [ErGr80]
- [Gu04]

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
