# Erdős #929 - Knowledge Base

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

Let $k\geq 2$ be large and let $S(k)$ be the minimal $x$ such that there is a positive density set of $n$ where\[n+1,n+2,\ldots,n+k\]are all divisible by primes $\leq x$.

Estimate $S(k)$ - in particular, is it true that $S(k)\geq k^{1-o(1)}$?



It follows from Rosser's sieve that $S(k)> k^{1/2-o(1)}$.

It is trivial that $S(k)\leq k+1$ since, for example, one can take $n\equiv 1\pmod{(k+1)!}$. The best bound on large gaps between primes due to Ford, Green, Konyagin, Maynard, and Tao \cite{FGKMT18} (see [4]) implies\[S(k) \ll k \frac{\log\log\log k}{\log\log k\log\log\log\log k}.\]




References


[FGKMT18] Ford, Kevin and Green, Ben and Konyagin, Sergei and Maynard, James and Tao, Terence, Long gaps between primes. J. Amer. Math. Soc. (2018), 65-105.


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
- Problem #4
- Problem #928
- Problem #930
- Problem #39
- Problem #1

## References

- Er76d
- FGKMT18

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-15*
