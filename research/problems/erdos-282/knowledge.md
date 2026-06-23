# Erdős #282 - Knowledge Base

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

Let $A\subseteq \mathbb{N}$ be an infinite set and consider the following greedy algorithm for a rational $x\in (0,1)$: choose the minimal $n\in A$ such that $n\geq 1/x$ and repeat with $x$ replaced by $x-\frac{1}{n}$. If this terminates after finitely many steps then this produces a representation of $x$ as the sum of distinct unit fractions with denominators from $A$.

Does this process always terminate if $x$ has odd denominator and $A$ is the set of odd numbers? More generally, for which pairs $x$ and $A$ does this process terminate?



In 1202 Fibonacci observed that this process terminates for any $x$ when $A=\mathbb{N}$. The problem when $A$ is the set of odd numbers is due to Stein.

Graham \cite{Gr64b} has shown that $\frac{m}{n}$ is the sum of distinct unit fractions with denominators $\equiv a\pmod{d}$ if and only if\[\left(\frac{n}{(n,(a,d))},\frac{d}{(a,d)}\right)=1.\]Does the greedy algorithm always terminate in such cases?

Graham \cite{Gr64c} has also shown that $x$ is the sum of distinct unit fractions with square denominators if and only if $x\in [0,\pi^2/6-1)\cup [1,\pi^2/6)$. Does the greedy algorithm for this always terminate? Erd\H{o}s and Graham believe not - indeed, perhaps it fails to terminate almost always.

See also [206].




References


[Gr64b] Graham, R. L., On finite sums of unit fractions. Proc. London Math. Soc. (3) (1964), 193-207.

[Gr64c] Graham, R. L., On finite sums of reciprocals of distinct nth powers. Pacific J. Math. (1964), 85-92.


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
- Problem #6
- Problem #206
- Problem #281
- Problem #283
- Problem #2
- Problem #39
- Problem #1

## References

- Gr64b
- Gr64c

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-12*
