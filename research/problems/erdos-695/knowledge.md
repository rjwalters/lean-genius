# Erdős #695 - Knowledge Base

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

Let $p_1<p_2<\cdots$ be a sequence of primes such that $p_{i+1}\equiv 1\pmod{p_i}$. Is it true that\[\lim_k p_k^{1/k}=\infty?\]Does there exist such a sequence with\[p_k \leq \exp(k(\log k)^{1+o(1)})?\]



Such a sequence is sometimes called a prime chain.

If we take the obvious 'greedy' chain with $2=p_1$ and $p_{i+1}$ is the smallest prime $\equiv 1\pmod{p_i}$ then Linnik's theorem implies that this sequence grows like\[p_k \leq e^{e^{O(k)}}.\]It is conjectured that, for any prime $p$, there is a prime $p'\leq p(\log p)^{O(1)}$ which is congruent to $1\pmod{p}$, which would imply this sequence grows like\[p_k\leq \exp(k(\log k)^{1+o(1)}).\]An extensive study of the growth of finite prime chains was carried out by Ford, Konyagin, and Luca \cite{FKL10}.

See also [696].




References


[FKL10] Ford, Kevin and Konyagin, Sergei V. and Luca, Florian, Prime chains and {P}ratt trees. Geom. Funct. Anal. (2010), 1231--1258.


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
- Problem #696
- Problem #694
- Problem #2
- Problem #39
- Problem #1

## References

- Er79e
- FKL10

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-14*
