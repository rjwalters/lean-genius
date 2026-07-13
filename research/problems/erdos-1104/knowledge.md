# Erdős #1104 - Knowledge Base

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

Let $f(n)$ be the maximum possible chromatic number of a triangle-free graph on $n$ vertices. Estimate $f(n)$.



The bounds $R(3,k)\asymp k^2/\log k$ (see [165]) imply $f(n) \asymp (n/\log n)^{1/2}$. The best bounds available are\[(1-o(1))(n/\log n)^{1/2}\leq f(n) \leq (2+o(1))(n/\log n)^{1/2}.\]The upper bound is due to Davies and Illingworth \cite{DaIl22}, the lower bound follows from a construction of Hefty, Horn, King, and Pfender \cite{HHKP25}.

One can ask a similar question for the maximum possible chromatic number of a triangle-free graph on $m$ edges. Let this be $g(m)$. Davies and Illingworth \cite{DaIl22} prove\[g(m) \leq (3^{5/3}+o(1))\left(\frac{m}{(\log m)^2}\right)^{1/3}.\]Kim \cite{Ki95} gave a construction which implies $g(m) \gg (m/(\log m)^2)^{1/3}$.




References


[DaIl22] Davies, Ewan and Illingworth, Freddie, The {$\chi$}-{R}amsey problem for triangle-free graphs. SIAM J. Discrete Math. (2022), 1124--1134.

[HHKP25] Z. Hefty, P. Horn, D. King, and F. Pfender, Improving $R(3,k)$ in just two bites. arXiv:2510.19718 (2025).

[Ki95] Kim, J. H., The Ramsey number $R(3,t)$ has order of magnitude $t^2/\log t$. Random Structures and Algorithms (1995), 173-207.


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
- Problem #165
- Problem #2
- Problem #3
- Problem #1103
- Problem #1105
- Problem #39
- Problem #1

## References

- Er67c
- DaIl22
- HHKP25
- Ki95

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-15*
