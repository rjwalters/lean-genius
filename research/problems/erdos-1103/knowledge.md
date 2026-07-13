# Erdős #1103 - Knowledge Base

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

Let $A$ be an infinite sequence of integers such that every $n\in A+A$ is squarefree. How fast must $A$ grow?



Erd\H{o}s notes there exists such a sequence which grows exponentially, but does not expect such a sequence of polynomial growth.

In \cite{Er81h} he asked whether there is an infinite sequence of integers $A$ such that, for every $a\in A$ and prime $p$, if\[a\equiv t\pmod{p^2}\]then $1\leq t<p^2/2$. He noted that such a sequence has the property that every $n\in A+A$ is squarefree. He wrote 'I am doubtful if such a sequence exists. I formulated this problem while writing these lines and must ask the indulgence of the reader if it turns out to be trivial.'

Indeed, there are trivially at most finitely many such $a$, since there cannot be any primes $p\in (a^{1/2},(2a)^{1/2}]$, but there exist primes in $(x,\sqrt{2}x)$ for all large $x$.

If $A=\{a_1<a_2<\cdots\}$ is such a sequence then van Doorn and Tao \cite{vDTa25} have shown that $a_j > 0.24j^{4/3}$ for all $j$, and further that there exists such a sequence (furthermore with squarefree terms) such that\[a_j < \exp(5j/\log j)\]for all large $j$. A superior lower bound of $a_j \gg j^{15/11-o(1)}$ had earlier been found by Konyagin \cite{Ko04} when considering the finite case [1109].

They also obtain further results for the generalisation from squarefree to $k$-free integers, and also replacing $A+A$ with $A\cup (A+A)\cup(A+A+A)$.

See also [1109] for the finite analogue of this problem.




References


[Er81h] Erd\H{o}s, P., Some problems and results on additive and multiplicative
number theory. Analytic number theory (Philadelphia, Pa., 1980) (1981), 171-182.

[Ko04] Konyagin, S. V., Problems of the set of square-free numbers. Izv. Ross. Akad. Nauk Ser. Mat. (2004), 63--90.

[vDTa25] W. van Doorn and T. Tao, Growth rates of sequences governed by the squarefree properties of its translates. arXiv:2512.01087 (2025).


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
- Problem #3
- Problem #11
- Problem #1109
- Problem #1102
- Problem #1104
- Problem #39
- Problem #1

## References

- Er81h
- Ko04

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-15*
