# Erdős #180 - Knowledge Base

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

If $\mathcal{F}$ is a finite set of finite graphs then $\mathrm{ex}(n;\mathcal{F})$ is the maximum number of edges a graph on $n$ vertices can have without containing any subgraphs from $\mathcal{F}$. Note that it is trivial that $\mathrm{ex}(n;\mathcal{F})\leq \mathrm{ex}(n;G)$ for every $G\in\mathcal{F}$.

Is it true that, for every $\mathcal{F}$, there exists $G\in\mathcal{F}$ such that\[\mathrm{ex}(n;G)\ll_{\mathcal{F}}\mathrm{ex}(n;\mathcal{F})?\]



A problem of Erd\H{o}s and Simonovits.

This is trivially true if $\mathcal{F}$ does not contain any bipartite graphs, since by the Erd\H{o}s-Stone theorem if $H\in\mathcal{F}$ has minimal chromatic number $r\geq 2$ then\[\mathrm{ex}(n;H)=\mathrm{ex}(n;\mathcal{F})=\left(\frac{r-2}{r-1}+o(1)\right)\binom{n}{2}.\]Erd\H{o}s and Simonovits observe that this is false for infinite families $\mathcal{F}$, e.g. the family of all cycles.


Hunter has provided the following 'folklore counterexample': if $\mathcal{F}=\{H_1,H_2\}$ where $H_1$ is a star and $H_2$ is a matching, both with at least two edges, then $\mathrm{ex}(n;\mathcal{F})\ll 1$, but $\mathrm{ex}(n;H_i)\asymp n$ for $1\leq i\leq 2$. This conjecture may still hold for all other $\mathcal{F}$.

See also [575] and the entry in the graphs problem collection.


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
- Problem #575
- Problem #179
- Problem #181
- Problem #2
- Problem #39
- Problem #1

## References

- ErSi82

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-12*
