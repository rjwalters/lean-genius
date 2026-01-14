# Erdős #684 - Knowledge Base

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

For $0\leq k\leq n$ write\[\binom{n}{k} = uv\]where the only primes dividing $u$ are in $[2,k]$ and the only primes dividing $v$ are in $(k,n]$.

Let $f(n)$ be the smallest $k$ such that $u>n^2$. Give bounds for $f(n)$.



A classical theorem of Mahler states that for any $\epsilon>0$ and integers $k$ and $l$ then, writing\[(n+1)\cdots (n+k) = ab\]where the only primes dividing $a$ are $\leq l$ and the only primes dividing $b$ are $>l$, we have $a < n^{1+\epsilon}$ for all sufficiently large (depending on $\epsilon,k,l$) $n$.

Mahler's theorem implies $f(n)\to \infty$ as $n\to \infty$, but is ineffective, and so gives no bounds on the growth of $f(n)$.

One can similarly ask for estimates on the smallest integer $f(n,k)$ such that if $m$ is the factor of $\binom{n}{k}$ containing all primes $\leq f(n,k)$ then $m > n^2$.


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
- Problem #683
- Problem #685
- Problem #2
- Problem #39
- Problem #1

## References

- Er79d

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-14*
