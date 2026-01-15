# Erdős #848 - Knowledge Base

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

Is the maximum size of a set $A\subseteq \{1,\ldots,N\}$ such that $ab+1$ is never squarefree (for all $a,b\in A$) achieved by taking those $n\equiv 7\pmod{25}$?



A problem of Erd\H{o}s and S\'{a}rk\"{o}zy.

van Doorn has sent the following argument which shows\[\lvert A\rvert \leq (0.108\cdots+o(1))N.\]The condition implies, in particular, that $a^2+1$ is divisible by $p^2$ for some prime $p$ for all $a\in A$. Furthermore, $a^2+1\equiv 0\pmod{p^2}$ has either $2$ or $0$ solutions, according to whether $p\equiv 1\pmod{4}$ or $p\equiv 3\pmod{4}$. It follows that every $a\in A$ belongs to one of $2$ residue classes for some prime $p\equiv 1\pmod{4}$, and hence, as $N\to \infty$,\[\frac{\lvert A\rvert}{N}\leq 2\sum_{p\equiv 1\pmod{4}}\frac{1}{p^2}\approx 0.108.\]Weisenberg has noted that this proof in fact gives the slightly better constant of $\approx 0.105$ (see the comments section).

This was solved for all sufficiently large $N$ by Sawhney in this note. In fact, Sawhney proves something slightly stronger, that there exists some constant $c>0$ such that if $\lvert A\rvert \geq (\frac{1}{25}-c)N$ and $N$ is large then $A$ is contained in either $\{ n\equiv 7\pmod{25}\}$ or $\{n\equiv 18\pmod{25}\}$.

See also [844].



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
- Problem #844
- Problem #847
- Problem #849
- Problem #2
- Problem #39
- Problem #1

## References

- (None available)

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-15*
