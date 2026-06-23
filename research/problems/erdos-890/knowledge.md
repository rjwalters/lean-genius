# Erdős #890 - Knowledge Base

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

If $\omega(n)$ counts the number of distinct prime factors of $n$, then is it true that, for every $k\geq 1$,\[\liminf_{n\to \infty}\sum_{0\leq i<k}\omega(n+i)\leq k+\pi(k)?\]Is it true that\[\limsup_{n\to \infty}\left(\sum_{0\leq i<k}\omega(n+i)\right) \frac{\log\log n}{\log n}=1?\]



A question of Erd\H{o}s and Selfridge \cite{ErSe67}, who observe that\[\liminf_{n\to \infty}\sum_{0\leq i<k}\omega(n+i)\geq k+\pi(k)-1\]for every $k$. This follows from P\'{o}lya's theorem that the set of $k$-smooth integers has unbounded gaps - indeed, $n(n+1)\cdots (n+k-1)$ is divisible by all primes $\leq k$ and, provided $n$ is large, all but at most one of $n,n+1,\ldots,n+k-1$ has a prime factor $>k$ by P\'{o}lya's theorem.

It is a classical fact that\[\limsup_{n\to \infty}\omega(n)\frac{\log\log n}{\log n}=1.\]




References


[ErSe67] Erd\H{o}s, P. and Selfridge, J. L., Some problems on the prime factors of consecutive integers. Illinois J. Math. (1967), 428--430.


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
- Problem #889
- Problem #891
- Problem #2
- Problem #39
- Problem #1

## References

- ErSe67

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-15*
