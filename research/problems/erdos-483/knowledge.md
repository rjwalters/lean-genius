# Erdős #483 - Knowledge Base

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

Let $f(k)$ be the minimal $N$ such that if $\{1,\ldots,N\}$ is $k$-coloured then there is a monochromatic solution to $a+b=c$. Estimate $f(k)$. In particular, is it true that $f(k) < c^k$ for some constant $c>0$?



The values of $f(k)$ are known as Schur numbers. The best-known bounds for large $k$ are\[(380)^{k/5}-O(1)\leq f(k) \leq \lfloor(e-\tfrac{1}{24}) k!\rfloor-1.\]The lower bound is due to Ageron, Casteras, Pellerin, Portella, Rimmel, and Tomasik \cite{ACPPRT21} (improving previous bounds of Exoo \cite{Ex94} and Fredricksen and Sweet \cite{FrSw00}) and the upper bound is due to Whitehead \cite{Wh73}. Note that $380^{1/5}\approx 3.2806$.

The known values of $f$ are $f(1)=2$, $f(2)=5$, $f(3)=14$, $f(4)=45$, and $f(5)=161$ (see A030126). (The equality $f(5)=161$ was established by Heule \cite{He17}).

See also [183] (in particular a folklore observation gives $f(k)\leq R(3;k)-1$).




References


[ACPPRT21] R. Ageron, P. Casteras, T. Pellerin, Y. Portella, A. Rimmel, and J. Tomasik, New lower bounds for Schur and weak Schur numbers. arXiv:2112.03175 (2021).

[Ex94] Exoo, G., A lower bound for Schur numbers and multicolor Ramsey numbers. Electronic J. of Combinatorics (1994).

[FrSw00] Fredricksen, Harold and Sweet, Melvin M., Symmetric sum-free partitions and lower bounds for {S}chur
numbers. Electron. J. Combin. (2000), Research Paper 32, 9.

[He17] M. Heuele, Schur Number Five. arXiv:1711.08076 (2017).

[Wh73] Whitehead, Jr., Earl Glen, The {R}amsey number {$N(3,\,3,\,3,\,3;\,2)$}. Discrete Math. (1973), 389--396.


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
- Problem #5
- Problem #183
- Problem #482
- Problem #484
- Problem #2
- Problem #39
- Problem #1
- Problem #20

## References

- ACPPRT21
- Ex94
- FrSw00
- Wh73
- He17

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-13*
