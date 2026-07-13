# Erdős #1105 - Knowledge Base

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

The anti-Ramsey number $\mathrm{AR}(n,G)$ is the maximum possible number of colours in which the edges of $K_n$ can be coloured without creating a rainbow copy of $G$ (i.e. one in which all edges have different colours).

Let $C_k$ be the cycle on $k$ vertices. Is it true that\[\mathrm{AR}(n,C_k)=\left(\frac{k-2}{2}+\frac{1}{k-1}\right)n+O(1)?\]Let $P_k$ be the path on $k$ vertices and $\ell=\lfloor\frac{k-1}{2}\rfloor$. If $n\geq k\geq 5$ then is $\mathrm{AR}(n,P_k)$ equal to\[\max\left(\binom{k-2}{2}+1, \binom{\ell-1}{2}+(\ell-1)(n-\ell+1)+\epsilon\right)\]where $\epsilon=1$ if $k$ is odd and $\epsilon=2$ otherwise?



A conjecture of Erd\H{o}s, Simonovits, and S\'{o}s \cite{ESS75}, who gave a simple proof that $\mathrm{AR}(n,C_3)=n-1$. In this paper they announced proofs of the claimed formula for $\mathrm{AR}(n,P_k)$ for $n\geq \frac{5}{4}k+C$ for some large constant $C$, and also for all $n\geq k$ if $k$ is sufficiently large, but these never appeared.

Simonovits and S\'{o}s \cite{SiSo84} published a proof that the claimed formula for $\mathrm{AR}(n,P_k)$ is true for $n\geq ck^2$ for some constant $c>0$.

A proof of the formula for $\mathrm{AR}(n,P_k)$ for all $n\geq k\geq 5$ has been announced by Yuan \cite{Yu21}




References


[ESS75] Erd\H{o}s, P. and Simonovits, M. and S\'os, V. T., Anti-{R}amsey theorems. (1975), 633--643.

[SiSo84] Simonovits, Mikl\'os and S\'os, Vera T., On restricted colourings of {$K_n$}. Combinatorica (1984), 101--110.

[Yu21] L.-T. Yuan, The anti-Ramsey number for paths. arXiv:2102.00807 (2021).


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
- Problem #1104
- Problem #1106
- Problem #2
- Problem #39
- Problem #1

## References

- ESS75
- SiSo84
- Yu21

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-15*
