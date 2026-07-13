# Erdős #1093 - Knowledge Base

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

For $n\geq 2k$ we define the deficiency of $\binom{n}{k}$ as follows. If $\binom{n}{k}$ is divisible by a prime $p\leq k$ then the deficiency is undefined. Otherwise, the deficiency is the number of $0\leq i<k$ such that $n-i$ is $k$-smooth, that is, divisible only by primes $\leq k$.

Are there infinitely many binomial coefficients with deficiency $1$? Are there only finitely many with deficiency $>1$?



A problem of Erd\H{o}s, Lacampagne, and Selfridge \cite{ELS88}, that was also asked in the 1986 problem session of West Coast Number Theory (as reported here).

In \cite{ELS93} they prove that if the deficiency exists and is $\geq 1$ then $n\ll 2^k\sqrt{k}$.

The following examples are either from \cite{ELS88} or here. The following have deficiency $1$ (there are $58$ examples with $n\leq 10^5$):\[\binom{7}{3},\binom{13}{4},\binom{14}{4},\binom{23}{5},\binom{62}{6},\binom{94}{10},\binom{95}{10}.\]The examples which follow are the only known examples with deficiency $>1$. The following have deficiency $2$:\[\binom{44}{8},\binom{74}{10},\binom{174}{12},\binom{239}{14},\binom{5179}{27},\binom{8413}{28},\binom{8414}{28},\binom{96622}{42}.\]The following have deficiency $3$:\[\binom{46}{10},\binom{47}{10},\binom{241}{16},\binom{2105}{25},\binom{1119}{27},\binom{6459}{33}.\]The following has deficiency $4$:\[\binom{47}{11}.\]The following has deficiency $9$:\[\binom{284}{28}.\]See also [384] and [1094].

Barreto in the comments has given a positive answer to the second question, conditional on two (strong) conjectures.




References


[ELS88] Erd\H{o}s, P. and Lacampagne, C. B. and Selfridge, J. L., Prime factors of binomial coefficients and related problems. Acta Arith. (1988), 507--523.

[ELS93] Erd\H{o}s, P. and Lacampagne, C. B. and Selfridge, J. L., Estimates of the least prime factor of a binomial coefficient. Math. Comp. (1993), 215--224.


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
- Problem #384
- Problem #1094
- Problem #1092
- Problem #39
- Problem #1

## References

- ELS88
- ELS93

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-15*
