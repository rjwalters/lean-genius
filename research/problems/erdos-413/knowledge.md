# Erdős #413 - Knowledge Base

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

Let $\omega(n)$ count the number of distinct primes dividing $n$. Are there infinitely many $n$ such that, for all $m<n$, we have $m+\omega(m) \leq n$?

Can one show that there exists an $\epsilon>0$ such that there are infinitely many $n$ where $m+\epsilon \omega(m)\leq n$ for all $m<n$?



In \cite{Er79} Erd\H{o}s calls such an $n$ a 'barrier' for $\omega$. Some other natural number theoretic functions (such as $\phi$ and $\sigma$) have no barriers because they increase too rapidly. Erd\H{o}s believed that $\omega$ should have infinitely many barriers. In \cite{Er79d} he proves that $F(n)=\prod k_i$, where $n=\prod p_i^{k_i}$, has infinitely many barriers (in fact the set of barriers has positive density in the integers).

Erd\H{o}s also believed that $\Omega$, the count of the number of prime factors with multiplicity), should have infinitely many barriers. Selfridge found the largest barrier for $\Omega$ which is $<10^5$ is $99840$.

In \cite{ErGr80} this problem is suggested as a way of showing that the iterated behaviour of $n\mapsto n+\omega(n)$ eventually settles into a single sequence, regardless of the starting value of $n$ (see also [412] and [414]).

Erd\H{o}s and Graham report it could be attacked by sieve methods, but 'at present these methods are not strong enough'.

See also [647] and [679].

The sequence of barriers for $\omega$ is A005236 in the OEIS.

This is discussed in problem B8 of Guy's collection \cite{Gu04}.




References


[Er79] Erd\H{o}s, Paul, Some unconventional problems in number theory. Math. Mag. (1979), 67-70.

[Er79d] Erd\H{o}s, P., Some unconventional problems in number theory. Acta Math. Acad. Sci. Hungar. (1979), 71-80.

[ErGr80] Erd\H{o}s, P. and Graham, R., Old and new problems and results in combinatorial number theory. Monographies de L'Enseignement Mathematique (1980).

[Gu04] Guy, Richard K., Unsolved problems in number theory. (2004), xviii+437.


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
- Problem #412
- Problem #414
- Problem #647
- Problem #679
- Problem #2
- Problem #39
- Problem #1

## References

- Er79
- Er79d
- Er92e
- Er95c
- ErGr80
- Gu04

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-13*
