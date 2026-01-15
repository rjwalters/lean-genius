# Erdős #1094 - Knowledge Base

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

For all $n\geq 2k$ the least prime factor of $\binom{n}{k}$ is $\leq \max(n/k,k)$, with only finitely many exceptions.



A stronger form of [384] that appears in a paper of Erd\H{o}s, Lacampagne, and Selfridge \cite{ELS88}. Erd\H{o}s observed that the least prime factor is always $\leq n/k$ provided $n$ is sufficiently large depending on $k$. Selfridge \cite{Se77} further conjectured that this always happens if $n\geq k^2-1$, except $\binom{62}{6}$.

The threshold $g(k)$ below which $\binom{n}{k}$ is guaranteed to be divisible by a prime $\leq k$ is the subject of [1095].

More precisely, in \cite{ELS88} they conjecture that if $n\geq 2k$ then the least prime factor of $\binom{n}{k}$ is $\leq \max(n/k,k)$ with the following $14$ exceptions:\[\binom{7}{3},\binom{13}{4},\binom{23}{5},\binom{14}{4},\binom{44}{8},\binom{46}{10},\binom{47}{10},\]\[\binom{47}{11},\binom{62}{6},\binom{74}{10},\binom{94}{10},\binom{95}{10},\binom{241}{16},\binom{284}{28}.\]They also suggest the stronger conjecture that, with a finite number of exceptions, the least prime factor is $\leq \max(n/k,\sqrt{k})$, or perhaps even $\leq \max(n/k,O(\log k))$. Indeed, in \cite{ELS93} they provide some further computational evidence, and point out it is consistent with what they know that in fact this holds with $\leq \max(n/k,13)$, with only $12$ exceptions.

Discussed in problem B31 and B33 of Guy's collection \cite{Gu04} - there Guy credits Selfridge with the conjecture that if $n> 17.125k$ then $\binom{n}{k}$ has a prime factor $p\leq n/k$.

This is related to [1093], in that the only counterexamples to this conjecture can occur from $\binom{n}{k}$ with deficiency $\geq 1$.

There is an interesting discussion about this problem on MathOverflow.




References


[ELS88] Erd\H{o}s, P. and Lacampagne, C. B. and Selfridge, J. L., Prime factors of binomial coefficients and related problems. Acta Arith. (1988), 507--523.

[ELS93] Erd\H{o}s, P. and Lacampagne, C. B. and Selfridge, J. L., Estimates of the least prime factor of a binomial coefficient. Math. Comp. (1993), 215--224.

[Gu04] Guy, Richard K., Unsolved problems in number theory. (2004), xviii+437.

[Se77] J. L. Selfridge, Some problems on the prime factors of consecutive integers. Notices Amer. Math. Soc. (1977), A456-457.


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
- Problem #384
- Problem #1095
- Problem #1093
- Problem #2
- Problem #39
- Problem #1
- Problem #25

## References

- ELS88
- ELS93
- Se77
- Gu04

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-15*
