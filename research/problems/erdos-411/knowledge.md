# Erdős #411 - Knowledge Base

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

Let $g_1=g(n)=n+\phi(n)$ and $g_k(n)=g(g_{k-1}(n))$. For which $n$ and $r$ is it true that $g_{k+r}(n)=2g_k(n)$ for all large $k$?



The known solutions to $g_{k+2}(n)=2g_k(n)$ are $n=10$ and $n=94$. Selfridge and Weintraub found solutions to $g_{k+9}(n)=9g_k(n)$ and Weintraub found\[g_{k+25}(3114)=729g_k(3114)\]for all $k\geq 6$.

Steinerberger \cite{St25} has observed that, for $r=2$, this problem is equivalent to asking for solutions to\[\phi(n)+\phi(n+\phi(n))=n,\]and has shown that if this holds then either the odd part of $n$ is in $\{1,3,5,7,35,47\}$, or is equal to $8m+7$ or $6m+5$, where $8m+7\geq 10^{10}$ is a prime number and $\phi(6m+5)=4m+4$. Whether there are infinitely many such $m$ is related to the question of whether\[\phi(n)=\frac{2}{3}(n+1)\]has infinitely many solutions.

Cambie conjectures that the only solutions have $r=2$ and $n=2^lp$ for some $l\geq 1$ and $p\in \{2,3,5,7,35,47\}$. Cambie has shown this problem is reducible to the question of which integers $r,t\geq 1$ and primes $p\equiv 7\pmod{8}$ satisfy $g_k(2p^t)=4p^t$, and conjectures there are no solutions to this except when $t=1$ and $p\in \{7,47\}$. Cambie has also observed that\[g_{k+4}(738)=3g_k(738),\]\[g_{k+4}(148646)=4g_k(148646),\]and\[g_{k+4}(4325798)=4g_{k}(4325798)\]for all $k\geq 1$.




References


[St25] S. Steinerberger, On an iterated arithmetic function problem of Erd\H{o}s and Graham. arXiv:2504.08023 (2025).


Back to the problem

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 3/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #1998
- Problem #410
- Problem #412
- Problem #2
- Problem #39
- Problem #1
- Problem #22

## References

- St25

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-13*
