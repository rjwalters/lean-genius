# Erdős #691 - Knowledge Base

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

Given $A\subseteq \mathbb{N}$ let $M_A=\{ n \geq 1 : a\mid n\textrm{ for some }a\in A\}$ be the set of multiples of $A$. Find a necessary and sufficient condition on $A$ for $M_A$ to have density $1$.



A sequence $A$ for which $M_A$ has density $1$ is called a Behrend sequence.

If $A$ is a set of prime numbers (or, more generally, a set of pairwise coprime integers without $1$) then a necessary and sufficient condition is that $\sum_{p\in A}\frac{1}{p}=\infty$.

The general situation is more complicated. For example suppose $A$ is the union of $(n_k,(1+\eta_k)n_k)\cap \mathbb{Z}$ where $1\leq n_1<n_2<\cdots$ is a lacunary sequence. (This construction is sometimes called a block sequence.) If $\sum \eta_k<\infty$ then the density of $M_A$ exists and is $<1$. If $\eta_k=1/k$, so $\sum \eta_k=\infty$, then the density exists and is $<1$.

Erd\H{o}s writes it 'seems certain' that there is some threshold $\alpha\in (0,1)$ such that, if $\eta_k=k^{-\beta}$, then the density of $M_A$ is $1$ if $\beta <\alpha$ and the density is $<1$ if $\beta >\alpha$.

Tenenbaum notes in \cite{Te96} that this is certainly not true as written since if the $n_j$ grow sufficiently quickly then this sequence is never Behrend, for any choice of $\eta_k$. He then writes 'we understand from subsequent discussions with Erd\H{o}s that he had actually in mind a two-sided condition on' $n_{j+1}/n_j$.

Tenenbaum \cite{Te96} proves this conjecture: if there are constants $1<C_1<C_2$ such that $C_1<n_{i+1}/n_i<C_2$ for all $i$ and $\eta_k=k^{-\beta}$ then $A$ is Behrend if $\beta<\log 2$ and not Behrend if $\beta>\log 2$.




References


[Te96] Tenenbaum, G., On block {B}ehrend sequences. Math. Proc. Cambridge Philos. Soc. (1996), 355--367.


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
- Problem #690
- Problem #692
- Problem #2
- Problem #39
- Problem #1

## References

- Te96

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-14*
