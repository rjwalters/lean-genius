# Erdős #358 - Knowledge Base

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

Let $A=\{a_1<\cdots\}$ be an infinite sequence of integers. Let $f(n)$ count the number of solutions to\[n=\sum_{u\leq i\leq v}a_i.\]Is there such an $A$ for which $f(n)\to \infty$ as $n\to \infty$? Or even where $f(n)\geq 2$ for all large $n$?





When $a_n=n$ the function $f(n)$ counts the number of odd divisors of $n$.

In modern language, this asks for the existence of a convex set $A$ such that $1_A\circ 1_A(n)\to \infty$ as $n\to \infty$.

Erd\H{o}s and Moser \cite{Mo63} considered the case when $A$ is the set of primes, and conjectured that the $\limsup$ of the number of such representations in this case is infinite. They could not even prove that the upper density of the set of integers representable in this form is positive.

In \cite{ErGr80} they further asked whether $f(n)\geq 1$ for all large $n$ is possible, but Egami observed the answer to this is trivially yes, taking $a_n=n$. Perhaps they intended to restrict $f(n)$ to only count those representatives as the sum of at least two consecutive terms. (It is a classical fact that $n$ can be expressed as a sum of at least two consecutive positive integers if and only if $n\neq 2^k$.)

In \cite{Er77c} Erd\H{o}s writes 'This problem can perhaps be rightly criticized as being artificial and in the backwater of Mathematics but it seems very strange and attractive to me'.

Weisenberg observes that the finite analogue of this problem, asking how many integers up to some $x$ can be written as the sum of consecutive elements, is very similar to [356].

This is reported in problem C2 of Guy's collection \cite{Gu04}.




References


[Er77c] Erd\H{o}s, Paul, Problems and results on combinatorial number theory. III. Number theory day (Proc. Conf., Rockefeller Univ.,
New York, 1976) (1977), 43-72.

[ErGr80] Erd\H{o}s, P. and Graham, R., Old and new problems and results in combinatorial number theory. Monographies de L'Enseignement Mathematique (1980).

[Gu04] Guy, Richard K., Unsolved problems in number theory. (2004), xviii+437.

[Mo63] Moser, L., Notes on number theory. III. On the sum of consecutive primes. Canad. Math. Bull. (1963), 159-161.


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
- Problem #356
- Problem #357
- Problem #359
- Problem #2
- Problem #39
- Problem #1

## References

- Er77c
- Mo63
- ErGr80
- Gu04

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-13*
