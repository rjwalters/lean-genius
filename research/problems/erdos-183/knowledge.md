# Erdős #183 - Knowledge Base

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

Let $R(3;k)$ be the minimal $n$ such that if the edges of $K_n$ are coloured with $k$ colours then there must exist a monochromatic triangle. Determine\[\lim_{k\to \infty}R(3;k)^{1/k}.\]



Erd\H{o}s offers \$100 for showing that this limit is finite. An easy pigeonhole argument shows that\[R(3;k)\leq 2+k(R(3;k-1)-1),\]from which $R(3;k)\leq \lceil e k!\rceil$ immediately follows. The best-known upper bounds are all of the form $ck!+O(1)$, and arise from this type of inductive relationship and computational bounds for $R(3;k)$ for small $k$. The best-known lower bound (coming from lower bounds for Schur numbers) is\[R(3,k)\geq (380)^{k/5}-O(1),\]due to Ageron, Casteras, Pellerin, Portella, Rimmel, and Tomasik \cite{ACPPRT21} (improving previous bounds of Exoo \cite{Ex94} and Fredricksen and Sweet \cite{FrSw00}). Note that $380^{1/5}\approx 3.2806$.

See also [483].

This problem is #21 in Ramsey Theory in the graphs problem collection.




References


[ACPPRT21] R. Ageron, P. Casteras, T. Pellerin, Y. Portella, A. Rimmel, and J. Tomasik, New lower bounds for Schur and weak Schur numbers. arXiv:2112.03175 (2021).

[Ex94] Exoo, G., A lower bound for Schur numbers and multicolor Ramsey numbers. Electronic J. of Combinatorics (1994).

[FrSw00] Fredricksen, Harold and Sweet, Melvin M., Symmetric sum-free partitions and lower bounds for {S}chur
numbers. Electron. J. Combin. (2000), Research Paper 32, 9.


Back to the problem

## Status

**Erdős Database Status**: OPEN
**Prize**: $250
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
- Problem #483
- Problem #21
- Problem #182
- Problem #184
- Problem #2
- Problem #39
- Problem #1

## References

- Er61
- ACPPRT21
- Ex94
- FrSw00

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-12*
