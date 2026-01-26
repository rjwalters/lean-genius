# Problem: Erdős #413

## Statement

### Plain Language
Let $\omega(n)$ count the number of distinct primes dividing $n$. Are there infinitely many $n$ such that, for all $m0$ such that there are infinitely many $n$ where $m+\epsilon \omega(m)\leq n$ for all $m<n$?



In \cite{Er79} Erd\H{o}s calls such an $n$ a 'barrier' for $\omega$. Some other natural number theoretic functions (such as $\phi$ and $\sigma$) have no barriers because they increase too rapidly. Erd\H{o}s belie...


### Formal Statement
$$
Let $\omega(n)$ count the number of distinct primes dividing $n$. Are there infinitely many $n$ such that, for all $m<n$, we have $m+\omega(m) \leq n$?

Can one show that there exists an $\epsilon>0$ such that there are infinitely many $n$ where $m+\epsilon \omega(m)\leq n$ for all $m<n$?



In \cite{Er79} Erd\H{o}s calls such an $n$ a 'barrier' for $\omega$. Some other natural number theoretic functions (such as $\phi$ and $\sigma$) have no barriers because they increase too rapidly. Erd\H{o}s believed that $\omega$ should have infinitely many barriers. In \cite{Er79d} he proves that $F(n)=\prod k_i$, where $n=\prod p_i^{k_i}$, has infinitely many barriers (in fact the set of barriers has positive density in the integers).

Erd\H{o}s also believed that $\Omega$, the count of the number of prime factors with multiplicity), should have infinitely many barriers. Selfridge found the largest barrier for $\Omega$ which is $<10^5$ is $99840$.

In \cite{ErGr80} this problem is suggested as a way of showing that the iterated behaviour of $n\mapsto n+\omega(n)$ eventually settles into a single sequence, regardless of the starting value of $n$ (see also [412] and [414]).

Erd\H{o}s and Graham report it could be attacked by sieve methods, but 'at present these methods are not strong enough'.

See also [647] and [679].

The sequence of barriers for $\omega$ is A005236 in the OEIS.

This is discussed in problem B8 of Guy's collection \cite{Gu04}.
$$

## Classification

```yaml
tier: C
significance: 5
tractability: 3
erdosNumber: 413
erdosUrl: https://erdosproblems.com/413

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
- [Problem #412](https://www.erdosproblems.com/412)
- [Problem #414](https://www.erdosproblems.com/414)
- [Problem #647](https://www.erdosproblems.com/647)
- [Problem #679](https://www.erdosproblems.com/679)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Er79]
- [Er79d]
- [Er92e]
- [Er95c]
- [ErGr80]
- [Gu04]

## OEIS Sequences

- [A005236](https://oeis.org/A005236)
- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
