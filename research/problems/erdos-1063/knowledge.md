# Erdős #1063 - Knowledge Base

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

Let $k\geq 2$ and define $n_k\geq 2k$ to be the least value of $n$ such that $n-i$ divides $\binom{n}{k}$ for all but one $0\leq i<k$. Estimate $n_k$.



A problem of Erd\H{o}s and Selfridge posed in \cite{ErSe83}. Erd\H{o}s and Selfridge noted (and a proof can be found in \cite{Mo85}) that if $n\geq 2k$ then there must exist at least one $0\leq i<k$ such that $n-i$ does not divide $\binom{n}{k}$.

We have $n_2=4$, $n_3=6$, $n_4=9$, and $n_5=12$. Monier \cite{Mo85} observed that $n_k\leq k!$ for $k\geq 3$, since $\binom{k!}{k}$ is divisible by $k!-i$ for $1\leq i<k$. Cambie observes in the comments that this can be improved to\[n_k\leq k[2,3,\ldots,k-1]\leq e^{(1+o(1))k},\]where $[\cdots]$ is the least common multiple.

This is discussed in problem B31 of Guy's collection \cite{Gu04}.




References


[ErSe83] Erdos, P. and Selfridge, J. L., Problem 6447. Amer. Math. Monthly (1983), 710.

[Gu04] Guy, Richard K., Unsolved problems in number theory. (2004), xviii+437.

[Mo85] No reference found.



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
- Problem #1062
- Problem #1064
- Problem #2
- Problem #39
- Problem #1

## References

- ErSe73
- ErSe83
- Mo85
- Gu04

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-15*
