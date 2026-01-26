# Problem: Erdős #684

## Statement

### Plain Language
For $0\leq k\leq n$ write\[\binom{n}{k} = uv\]where the only primes dividing $u$ are in $[2,k]$ and the only primes dividing $v$ are in $(k,n]$.

Let $f(n)$ be the smallest $k$ such that $u>n^2$. Give bounds for $f(n)$.



A classical theorem of Mahler states that for any $\epsilon>0$ and integers $k$ and $l$ then, writing\[(n+1)\cdots (n+k) = ab\]where the only primes dividing $a$ are $\leq l$ and the only primes dividin...


### Formal Statement
$$
For $0\leq k\leq n$ write\[\binom{n}{k} = uv\]where the only primes dividing $u$ are in $[2,k]$ and the only primes dividing $v$ are in $(k,n]$.

Let $f(n)$ be the smallest $k$ such that $u>n^2$. Give bounds for $f(n)$.



A classical theorem of Mahler states that for any $\epsilon>0$ and integers $k$ and $l$ then, writing\[(n+1)\cdots (n+k) = ab\]where the only primes dividing $a$ are $\leq l$ and the only primes dividing $b$ are $>l$, we have $a < n^{1+\epsilon}$ for all sufficiently large (depending on $\epsilon,k,l$) $n$.

Mahler's theorem implies $f(n)\to \infty$ as $n\to \infty$, but is ineffective, and so gives no bounds on the growth of $f(n)$.

One can similarly ask for estimates on the smallest integer $f(n,k)$ such that if $m$ is the factor of $\binom{n}{k}$ containing all primes $\leq f(n,k)$ then $m > n^2$.
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 684
erdosUrl: https://erdosproblems.com/684

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
- [Problem #683](https://www.erdosproblems.com/683)
- [Problem #685](https://www.erdosproblems.com/685)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Er79d]

## OEIS Sequences

- [A392019](https://oeis.org/A392019)
- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
