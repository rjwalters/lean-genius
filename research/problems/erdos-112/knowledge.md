# Erdős #112 - Knowledge Base

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

Let $k=k(n,m)$ be minimal such that any directed graph on $k$ vertices must contain either an independent set of size $n$ or a transitive tournament of size $m$. Determine $k(n,m)$.



A problem of Erd\H{o}s and Rado \cite{ErRa67}, who showed $k(n,m) \ll_m n^{m-1}$, or more precisely,\[k(n,m) \leq \frac{2^{m-1}(n-1)^m+n-2}{2n-3}.\]Larson and Mitchell \cite{LaMi97} improved the dependence on $m$, establishing in particular that $k(n,3)\leq n^{2}$. Zach Hunter has observed that\[R(n,m) \leq k(n,m)\leq R(n,m,m),\]which in particular proves the upper bound $k(n,m)\leq 3^{n+2m}$.


See also the entry in the graphs problem collection - on this site the problem replaces transitive tournament with directed path, but Zach Hunter and Raphael Steiner have a simple argument that proves, for this alternative definition, that $k(n,m)=(n-1)(m-1)$.




References


[ErRa67] Erd\H{o}s, P. and Rado, R., Partition relations and transitivity domains of binary
relations. J. London Math. Soc. (1967), 624-633.

[LaMi97] Larson, Jean A. and Mitchell, William J., On a problem of Erd\H{o}s and Rado. Ann. Comb. (1997), 245-252.


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
- Problem #111
- Problem #113
- Problem #2
- Problem #39
- Problem #1

## References

- ErRa67
- LaMi97

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-12*
