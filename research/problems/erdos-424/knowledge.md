# Erdős #424 - Knowledge Base

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

Let $a_1=2$ and $a_2=3$ and continue the sequence by appending to $a_1,\ldots,a_n$ all possible values of $a_ia_j-1$ with $i\neq j$. Is it true that the set of integers which eventually appear has positive density?



Asked by Hofstadter. The sequence begins $2,3,5,9,14,17,26,\ldots$ and is A005244 in the OEIS. This problem is also discussed in section E31 of Guy's book Unsolved Problems in Number Theory.

In \cite{ErGr80} (and in Guy's book) this problem as written is asking for whether almost all integers appear in this sequence, but the answer to this is trivially no (as pointed out to me by Steinerberger): no integer $\equiv 1\pmod{3}$ is ever in the sequence, so the set of integers which appear has density at most $2/3$. This is easily seen by induction, and the fact that if $a,b\in \{0,2\}\pmod{3}$ then $ab-1\in \{0,2\}\pmod{3}$.

Presumably it is the weaker question of whether a positive density of integers appear (as correctly asked in \cite{Er77c}) that was also intended in \cite{ErGr80}.

See also Problem 63 of Green's open problems list.




References


[Er77c] Erd\H{o}s, Paul, Problems and results on combinatorial number theory. III. Number theory day (Proc. Conf., Rockefeller Univ.,
New York, 1976) (1977), 43-72.

[ErGr80] Erd\H{o}s, P. and Graham, R., Old and new problems and results in combinatorial number theory. Monographies de L'Enseignement Mathematique (1980).


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
- Problem #3
- Problem #423
- Problem #425
- Problem #2
- Problem #39
- Problem #1
- Problem #63

## References

- ErGr80
- Er77c

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-13*
