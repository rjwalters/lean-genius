# Erdős #319 - Knowledge Base

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

What is the size of the largest $A\subseteq \{1,\ldots,N\}$ such that there is a function $\delta:A\to \{-1,1\}$ such that\[\sum_{n\in A}\frac{\delta_n}{n}=0\]and\[\sum_{n\in A'}\frac{\delta_n}{n}\neq 0\]for all non-empty $A'\subsetneq A$?



Adenwalla has observed that a lower bound of\[\lvert A\rvert\geq (1-\tfrac{1}{e}+o(1))N\]follows from the main result of Croot \cite{Cr01}, which states that there exists some set of integers $B\subset [(\frac{1}{e}-o(1))N,N]$ such that $\sum_{b\in B}\frac{1}{b}=1$. Since the sum of $\frac{1}{m}$ for $m\in [c_1N,c_2N]$ is asymptotic to $\log(c_2/c_1)$ we must have $\lvert B\rvert \geq (1-\tfrac{1}{e}+o(1))N$.

We may then let $A=B\cup\{1\}$ and choose $\delta(n)=-1$ for all $n\in B$ and $\delta(1)=1$.

This problem has been formalised in Lean as part of the Google DeepMind Formal Conjectures project.




References


[Cr01] Croot, III, Ernest S., On unit fractions with denominators in short intervals. Acta Arith. (2001), 99-114.


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
- Problem #318
- Problem #320
- Problem #2
- Problem #39
- Problem #1

## References

- ErGr80
- Cr01

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-12*
