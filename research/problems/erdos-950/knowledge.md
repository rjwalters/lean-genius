# Erdős #950 - Knowledge Base

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

Let\[f(n) = \sum_{p<n}\frac{1}{n-p}.\]Is it true that\[\liminf f(n)=1\]and\[\limsup f(n)=\infty?\]Is it true that $f(n)=o(\log\log n)$ for all $n$?



This function was considered by de Bruijn, Erd\H{o}s, and Tur\'{a}n, who showed that\[\sum_{n<x}f(n)\sim \sum_{n<x}f(n)^2\sim x.\]The existence of some $c>0$ such that there are $\gg n^c/\log n$ many primes in $[n,n+n^c]$ implies that $\liminf f(n)>0$.

Erd\H{o}s writes that a 'weaker conjecture which is perhaps not quite inaccessible' is that, for every $\epsilon>0$, if $x$ is sufficiently large there exists $y<x$ such that\[\pi(x)< \pi(y)+\epsilon \pi(x-y).\](Compare this to [855].) He notes that if\[\pi(x)< \pi(y)+O\left(\frac{x-y}{\log x}\right)\]for all $y<x-(\log x)^C$ for some constant $C>0$ then $f(n)\ll \log\log\log n$.

The study of $f(p)$ is even harder, and Erd\H{o}s could not prove that\[\sum_{p<x}f(p)^2\sim \pi(x).\]


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
- Problem #855
- Problem #949
- Problem #951
- Problem #2
- Problem #39
- Problem #1

## References

- Er77c

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-15*
