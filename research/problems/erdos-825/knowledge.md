# Erdős #825 - Knowledge Base

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

Is there an absolute constant $C>0$ such that every integer $n$ with $\sigma(n)>Cn$ is the distinct sum of proper divisors of $n$?



A problem of Benkoski and Erd\H{o}s. In other words, this problem asks for an upper bound for the abundancy index of weird numbers. This could be true with $C=3$. We must have $C>2$ since $\sigma(70)=144$ but $70$ is not the distinct sum of integers from $\{1,2,5,7,10,14,35\}$.

Erd\H{o}s suggested that as $C\to \infty$ only divisors at most $\epsilon n$ need to be used, where $\epsilon \to 0$.

Weisenberg has observed that if $n$ is a weird number with an abundancy index $\geq 4$ then it is divisible by an odd weird number. In particular, if there are no odd weird numbers (see [470]) then every weird number has abundancy index $<4$. Indeed, if $l(n)$ is the abundancy index and $n=2^km$ with $m$ odd then $l(n)=l(2^k)l(m)$, and $l(2^k)<2$ so if $l(n)\geq 4$ then $l(m)>2$, and hence $m$ is weird (as a factor of a weird number).

A similar argument shows that either there are infinitely many primitive weird numbers or there is an upper bound for the abundancy index of all weird numbers.

See also [18] and [470].

This is part of problem B2 in Guy's collection \cite{Gu04} (the \$25 is reported by Guy as offered by Erd\H{o}s for a solution to this question).




References


[Gu04] Guy, Richard K., Unsolved problems in number theory. (2004), xviii+437.


Back to the problem

## Status

**Erdős Database Status**: OPEN
**Prize**: $25
**Tractability Score**: 4/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #1998
- Problem #470
- Problem #18
- Problem #824
- Problem #826
- Problem #2
- Problem #39
- Problem #1

## References

- BeEr74
- Er74b
- Er96b
- Gu04

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-15*
