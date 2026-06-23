# Erdős #382 - Knowledge Base

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

Let $u\leq v$ be such that the largest prime dividing $\prod_{u\leq m\leq v}m$ appears with exponent at least $2$. Is it true that $v-u=v^{o(1)}$? Can $v-u$ be arbitrarily large?



Erd\H{o}s and Graham report it follows from results of Ramachandra that $v-u\leq v^{1/2+o(1)}$.

Cambie has observed that the first question boils down to some old conjectures on prime gaps.
By Cram\'{er's conjecture}, for every $\epsilon>0,$ for every $u$ sufficiently large there is a prime between $u$ and $u+u^\epsilon$.
Thus for $u+u^\epsilon<v$, the largest prime divisor of \( \prod_{u \leq m \leq v} m \) appears with exponent $1$.
Since this is not the case in the question, \( v - u = v^{o(1)} \).

Cambie also gives the following heuristic for the second question. The 'probability' that the largest prime divisor of $n$ is $<n^{1/2}$ is $1-\log 2>0$. For any fixed $k$, there is therefore a positive 'probability' that there are $k$ consecutive integers around $q^2$ (for a prime $q$) all of whose prime divisors are bounded above by $q$, when $v-u\geq k$. See [383] for a conjecture along these lines. A similar argument applies if we replace multiplicity $2$ with multiplicity $r$, for any fixed $r\geq 2$.

See also [380].


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
- Problem #2
- Problem #383
- Problem #380
- Problem #381
- Problem #39
- Problem #1

## References

- ErGr80

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-13*
