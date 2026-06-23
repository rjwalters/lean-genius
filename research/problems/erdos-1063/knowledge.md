# Erdős #1063 - Knowledge Base

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

Let $k\geq 2$ and define $n_k\geq 2k$ to be the least value of $n$ such that $n-i$ divides $\binom{n}{k}$ for all but one $0\leq i<k$. Estimate $n_k$.



A problem of Erd\H{o}s and Selfridge posed in \cite{ErSe83}. Erd\H{o}s and Selfridge noted (and a proof can be found in \cite{Mo85}) that if $n\geq 2k$ then there must exist at least one $0\leq i<k$ such that $n-i$ does not divide $\binom{n}{k}$.

We have $n_2=4$, $n_3=6$, $n_4=9$, and $n_5=12$. Monier \cite{Mo85} observed that $n_k\leq k!$ for $k\geq 3$, since $\binom{k!}{k}$ is divisible by $k!-i$ for $1\leq i<k$. Cambie observes in the comments that this can be improved to\[n_k\leq k[2,3,\ldots,k-1]\leq e^{(1+o(1))k},\]where $[\cdots]$ is the least common multiple.

This is discussed in problem B31 of Guy's collection \cite{Gu04}.




References


[ErSe83] Erdos, P. and Selfridge, J. L., Problem 6447. Amer. Math. Monthly (1983), 710.

[Gu04] Guy, Richard K., Unsolved problems in number theory. (2004), xviii+437.

[Mo85] No reference found.



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
- Problem #1062
- Problem #1064
- Problem #2
- Problem #39
- Problem #1

## References

- ErSe73
- ErSe83
- Mo85
- Gu04

## Sessions

### 2026-06-06 (researcher-1) — Session 1: unified existence + build verification

**Mode**: ACT (small addition + verification)
**Outcome**: Docker build clean (3058 jobs); added `threshold_exists` (1 new theorem).

#### What I added

A unified existence theorem `threshold_exists` (k ≥ 2) covering both:

- The k = 2 small-case witness from `threshold_k2` (n_2 = 4).
- The k ≥ 3 cases via `monier_factorial_bound`'s extracted threshold.

```lean
theorem threshold_exists (k : ℕ) (hk : k ≥ 2) :
    ∃ nk : ℕ, IsThreshold nk k := by
  by_cases h3 : k ≥ 3
  · obtain ⟨nk, hth, _⟩ := monier_factorial_bound k h3
    exact ⟨nk, hth⟩
  · have : k = 2 := by omega
    subst this
    exact ⟨4, threshold_k2⟩
```

This is a small "API smoothing" lemma: it presents the existence
question as a single uniform statement, decoupled from the specific
size bound (`k!` from Monier or `k · (k-1)!` from Cambie). Useful
downstream when one needs the bare existence rather than a sized
witness.

#### File status after S1

- 169 → 187 lines (theorem + docstring + section header).
- 5 → 6 theorems, 3 axioms unchanged, 0 sorries.
- Phase: ACT.

#### Honest assessment

Small API addition, not progress on the open question. The Erdős
Problem 1063 (polynomial vs exponential growth of n_k) remains
OPEN — and is unchanged here. Lasting value: future researchers
can use `threshold_exists` as a uniform interface to the
small-case witnesses + Monier's bound, instead of dispatching
manually on k.

The main open conjecture `ErdosProblem1063` (existence of a
polynomial bound) is unchanged.

#### Next steps

1. Strengthen `threshold_exists` to include Cambie's tighter bound
   `nk ≤ k * (k-1)!` (currently just gives bare existence).
2. Compute `n_6, n_7` via `native_decide` to extend the
   `threshold_k2..5` table.
3. Investigate whether `ErdosProblem1063` (polynomial bound)
   admits any verifiable conditional/partial result.

---

*Generated from erdosproblems.com on 2026-01-15*
