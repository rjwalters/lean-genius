# Problem: Erdős #380

## Statement

### Plain Language
We call an interval $[u,v]$ 'bad' if the greatest prime factor of $\prod_{u\leq m\leq v}m$ occurs with an exponent greater than $1$. Let $B(x)$ count the number of $n\leq x$ which are contained in at least one bad interval. Is it true that\[B(x)\sim \#\{ n\leq x: P(n)^2\mid n\},\]where $P(n)$ is the largest prime factor of $n$?



Erd\H{o}s and Graham only knew that $B(x) > x^{1-o(1)}$. Similarly, we call an interval $[u,...


### Formal Statement
$$
We call an interval $[u,v]$ 'bad' if the greatest prime factor of $\prod_{u\leq m\leq v}m$ occurs with an exponent greater than $1$. Let $B(x)$ count the number of $n\leq x$ which are contained in at least one bad interval. Is it true that\[B(x)\sim \#\{ n\leq x: P(n)^2\mid n\},\]where $P(n)$ is the largest prime factor of $n$?



Erd\H{o}s and Graham only knew that $B(x) > x^{1-o(1)}$. Similarly, we call an interval $[u,v]$ 'very bad' if $\prod_{u\leq m\leq v}m$ is powerful. The number of integers $n\leq x$ contained in at least one very bad interval should be $\ll x^{1/2}$. In fact, it should be asymptotic to the number of powerful numbers $\leq x$.

We have\[\#\{ n\leq x: P(n)^2\mid n\}=\frac{x}{\exp((c+o(1))\sqrt{\log x\log\log x})}\]for some constant $c>0$.

Tao notes in the comments that if $[u,v]$ is bad then it cannot contain any primes, and hence certainly $v<2u$, and in general $v-u$ must be small (for example, assuming Cramer's conjecture, $v-u\ll (\log u)^2$).

See also [382].
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 380
erdosUrl: https://erdosproblems.com/380

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
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #382](https://www.erdosproblems.com/382)
- [Problem #379](https://www.erdosproblems.com/379)
- [Problem #381](https://www.erdosproblems.com/381)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

(No references available)

## OEIS Sequences

- [A070003](https://oeis.org/A070003)
- [A388654](https://oeis.org/A388654)
- [A387054](https://oeis.org/A387054)
- [A389100](https://oeis.org/A389100)
- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
