# Erdős #700 - Knowledge Base

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

Let\[f(n)=\min_{1<k\leq n/2}\textrm{gcd}\left(n,\binom{n}{k}\right).\]{UL}
{LI}Characterise those composite $n$ such that $f(n)=n/P(n)$, where $P(n)$ is the largest prime dividing $n$.{/LI}
{LI}Are there infinitely many composite $n$ such that $f(n)>n^{1/2}$?{/LI}
{LI} Is it true that, for every composite $n$,\[f(n) \ll_A \frac{n}{(\log n)^A}\]for every $A>0$?{/LI}
{/UL}



A problem of Erd\H{o}s and Szekeres. It is easy to see that $f(n)\leq n/P(n)$ for composite $n$, since if $j=p^k$ where $p^k\mid n$ and $p^{k+1}\nmid n$ then $\textrm{gcd}\left(n,\binom{n}{j}\right)=n/p^k$. This implies\[f(n) \leq (1+o(1))\frac{n}{\log n}.\]It is known that $f(n)=n/P(n)$ when $n$ is the product of two primes. Another example is $n=30$.

For the second problem, it is easy to see that for any $n$ we have $f(n)\geq p(n)$, where $p(n)$ is the smallest prime dividing $n$, and hence there are infinitely many $n$ (those $=p^2)$ such that $f(n)\geq n^{1/2}$.


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
- Problem #699
- Problem #701
- Problem #39
- Problem #1

## References

- ErSz78

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-14*
