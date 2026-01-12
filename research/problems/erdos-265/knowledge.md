# Erdős #265 - Knowledge Base

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

How fast can $a_n\to \infty$ grow if\[\sum\frac{1}{a_n}\quad\textrm{and}\quad\sum\frac{1}{a_n-1}\]are both rational?



Cantor observed that $a_n=\binom{n}{2}$ is such a sequence. If we replace $-1$ by a different constant then higher degree polynomials can be used - for example if we consider $\sum_{n\geq 2}\frac{1}{a_n}$ and $\sum_{n\geq 2}\frac{1}{a_n-12}$ then $a_n=n^3+6n^2+5n$ is an example of both series being rational.

Erd\H{o}s believed that $a_n^{1/n}\to \infty$ is possible, but $a_n^{1/2^n}\to 1$ is necessary.

This has been almost completely solved by Kova\v{c} and Tao \cite{KoTa24}, who prove that such a sequence can grow doubly exponentially. More precisely, there exists such a sequence such that $a_n^{1/\beta^n}\to \infty$ for some $\beta >1$.

It remains open whether one can achieve\[\limsup a_n^{1/2^n}>1.\]A folklore result states that $\sum \frac{1}{a_n}$ is irrational whenever $\lim a_n^{1/2^n}=\infty$, and hence such a sequence cannot grow faster than doubly exponentially - the remaining question is the precise exponent possible.




References


[KoTa24] Kova\vC, V. and Tao T., On several irrationality problems for Ahmes series. arXiv:2406.17593 (2024).


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
- Problem #2
- Problem #264
- Problem #266
- Problem #39
- Problem #1

## References

- KoTa24

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-12*
