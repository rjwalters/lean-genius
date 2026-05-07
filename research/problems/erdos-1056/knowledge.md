# Erdős #1056 - Knowledge Base

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

Let $k\geq 2$. Does there exist a prime $p$ and consecutive intervals $I_1,\ldots,I_k$ such that\[\prod_{n\in I_i}n \equiv 1\pmod{p}\]for all $1\leq i\leq k$?



This is problem A15 in Guy's collection \cite{Gu04}, where he reports that in a letter in 1979 Erd\H{o}s observed that\[3\cdot 4\equiv 5\cdot 6\cdot 7\equiv 1\pmod{11},\]establishing the case $k=2$. Makowski \cite{Ma83} found, for $k=3$,\[2\cdot 3\cdot 4\cdot 5\equiv 6\cdot 7\cdot 8\cdot 9\cdot 10\cdot 11\equiv 12\cdot 13\cdot 14\cdot 15\equiv 1\pmod{17}.\]Noll and Simmons asked, more generally, whether there are solutions to $q_1!\equiv\cdots \equiv q_k!\pmod{p}$ for arbitrarily large $k$ (with $q_1<\cdots<q_k$).




References


[Gu04] Guy, Richard K., Unsolved problems in number theory. (2004), xviii+437.

[Ma83] M\polhk akowski, Andrzej, On a number-theoretical problem of {E}rd\H{o}s. Elem. Math. (1983), 101--102.


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
- Problem #1055
- Problem #1057
- Problem #2
- Problem #39
- Problem #1

## References

- Gu04
- Ma83

## Sessions

### Session 1 (prior, 2026-03)
Created Erdos1056Aristotle.lean companion file proving Wilson's constraint via Mathlib (ZMod.wilsons_lemma). Eliminated 3 sorries.

### Session 2 (researcher-7, 2026-05-07)
Extended verified k from {2,3,4,5,6} to {2,3,4,5,6,7,8,9} in Erdos1056OQ01.lean.

**Method**: Reformulate as factorial-collision problem. Solutions ↔ chains b₀ < … < bₖ with all bᵢ! ≡ same residue mod p. For each prime p, the largest residue class in (0!, 1!, …, (p-1)!) mod p determines the maximum k. With consecutive gaps ≥ 2 (no degenerate intervals), exhaustive search over primes ≤ 5000 finds:

| k | smallest p | factorial indices | residue |
|---|---|---|---|
| 2 | 11 | {0,1,9} | 1 |
| 3 | 17 | {0,1,5,11,15} (subset) | 1 |
| 4 | 23 | {0,1,4,8,11,21} (subset) | 1 |
| 5 | 109 | {9,11,39,58,73,85} | varies |
| 6 | 71 | {7,9,19,51,61,63,70} | 70 |
| 7 | 673 | {159,316,354,393,397,506,545,647} | varies |
| 8 | 599 | {28,50,122,183,250,289,500,539,555} | 175 |
| 9 | 3011 | {0,611,723,749,805,2205,2261,2287,2399,3009} | 1 |

**Surprising observation**: Smallest p is NOT monotone in k. p=599 < p=673 even though k=8 > k=7. A favorable prime can support a longer chain at smaller p.

**For k=10**: Need primes >5000. Found p=27901 as a witness (not necessarily smallest). Search to 30000 left as future work.

**Remaining axioms**: 1 (`erdos_1056_conjecture` in main file — the open conjecture itself).

---

*Generated from erdosproblems.com on 2026-01-15*
