# Erdős #380 - Knowledge Base

## Problem Statement

Forum
Favourites
Tags
More
 Go
 Go
Dual View
Random Solved
Random Open

We call an interval $[u,v]$ 'bad' if the greatest prime factor of $\prod_{u\leq m\leq v}m$ occurs with an exponent greater than $1$. Let $B(x)$ count the number of $n\leq x$ which are contained in at least one bad interval. Is it true that\[B(x)\sim \#\{ n\leq x: P(n)^2\mid n\},\]where $P(n)$ is the largest prime factor of $n$?



Erd\H{o}s and Graham only knew that $B(x) > x^{1-o(1)}$. Similarly, we call an interval $[u,v]$ 'very bad' if $\prod_{u\leq m\leq v}m$ is powerful. The number of integers $n\leq x$ contained in at least one very bad interval should be $\ll x^{1/2}$. In fact, it should be asymptotic to the number of powerful numbers $\leq x$.

We have\[\#\{ n\leq x: P(n)^2\mid n\}=\frac{x}{\exp((c+o(1))\sqrt{\log x\log\log x})}\]for some constant $c>0$.

Tao notes in the comments that if $[u,v]$ is bad then it cannot contain any primes, and hence certainly $v<2u$, and in general $v-u$ must be small (for example, assuming Cramer's conjecture, $v-u\ll (\log u)^2$).

See also [382].


Back to the problem

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 4/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #1998
- Problem #2
- Problem #382
- Problem #379
- Problem #381
- Problem #39
- Problem #1

## References

- (None available)

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-13*
