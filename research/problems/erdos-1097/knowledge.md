# Erdős #1097 - Knowledge Base

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

Let $A$ be a set of $n$ integers. How many distinct $d$ can occur as the common difference of a three-term arithmetic progression in $A$? Are there always $O(n^{3/2})$ many such $d$?



A problem Erd\H{o}s posed in the 1989 problem session of Great Western Number Theory.

He states that Erd\H{o}s and Ruzsa gave an explicit construction which achieved $n^{1+c}$ for some $c>0$, and Erd\H{o}s and Spencer gave a probabilistic proof which achieved $n^{3/2}$, and speculated this may be the best possible.

In the comment section, Chan has noticed that this problem is exactly equivalent to a sums-differences question of Bourgain \cite{Bo99}, introduced as an arithmetic path towards the Kakeya conjecture: find the smallest $c\in [1,2]$ such that, for any finite sets of integers $A$ and $B$ and $G\subseteq A\times B$ we have\[\lvert A\overset{G}{-}B\rvert \ll \max(\lvert A\rvert,\lvert B\rvert, \lvert A\overset{G}{+}B\rvert)^c\](where, for example, $A\overset{G}{+}B$ denotes the set of $a+b$ with $(a,b)\in G$).

This is equivalent in the sense that the greatest exponent $c$ achievable for the main problem here is equal to the smallest constant achievable for the sums-differences question. The current best bounds known are thus\[1.77898\cdots \leq c \leq 11/6 \approx 1.833.\]The upper bound is due to Katz and Tao \cite{KaTa99}. The lower bound is due to Lemm \cite{Le15} (with a very small improvement found by AlphaEvolve \cite{GGTW25}).





References


[Bo99] Bourgain, J., On the dimension of {K}akeya sets and related maximal
inequalities. Geom. Funct. Anal. (1999), 256--282.

[GGTW25] B. Georgiev, J. G\'{o}mez-Serrano, T. Tao, and A. Wagner, Mathematical exploration and discovery at scale. arXiv:2511.02864 (2025).

[KaTa99] Katz, Nets Hawk and Tao, Terence, Bounds on arithmetic projections, and applications to the
{K}akeya conjecture. Math. Res. Lett. (1999), 625--630.

[Le15] Lemm, Marius, New counterexamples for sums-differences. Proc. Amer. Math. Soc. (2015), 3863--3868.


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
- Problem #2
- Problem #6
- Problem #1096
- Problem #1098
- Problem #39
- Problem #1

## References

- GWNT89
- Bo99
- KaTa99
- Le15
- GGTW25

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-15*
