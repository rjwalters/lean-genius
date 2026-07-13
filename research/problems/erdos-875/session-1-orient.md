# Session 1 — ORIENT: Deshouillers–Erdős admissible sequences

**Date**: 2026-06-09
**Researcher**: researcher-6
**Phase**: ORIENT (NEW problem, prior knowledge tier = MODERATE per claim signal but research scaffold was empty)

## Problem (restated)

A strictly increasing infinite set $A=\{a_1<a_2<\cdots\}\subset \mathbb{N}$ is **admissible** if the sets
$$S_r := \{\, a_{i_1}+\cdots+a_{i_r} : i_1<\cdots<i_r \,\} \subseteq \mathbb{N}, \qquad r\ge 1,$$
are pairwise disjoint: $S_r\cap S_{r'}=\emptyset$ whenever $r\ne r'$.

Equivalently: a positive integer $v$ that is a sum of $r$ distinct elements of $A$ is never simultaneously a sum of $r'$ distinct elements for any $r'\ne r$. The cardinality of the representing subset is therefore a function of the value alone (when one exists).

Erdős–Deshouillers ask:

1. **Growth (upper).** How fast must $a_n$ grow?
2. **Gaps (lower).** How small can $a_{n+1}-a_n$ be?
3. **Polynomial-gap question.** For which $c\in\mathbb{R}_{>0}$ can one have $a_{n+1}-a_n\le n^{c}$ for all (or infinitely many) $n$?

Erdős further remarks that "it is not completely trivial to find such a sequence for which $a_{n+1}/a_n\to 1$"; whether Deshouillers–Erdős had such a construction in hand at the time of writing [Er98] is not clear from the wording. This is the infinite version of problem #874.

## Trivial existence: $A = \{2^{n-1}\}_{n\ge 1}$

**Claim.** $A=\{1,2,4,8,16,\dots\}$ is admissible.

**Proof.** Every positive integer $v$ has a *unique* representation as a sum of distinct powers of $2$ (its binary expansion). If $v\in S_r\cap S_{r'}$, then the binary representation of $v$ has both popcount $r$ and popcount $r'$, hence $r=r'$. $\square$

This establishes existence of admissible sequences. The growth rate is geometric ($a_n=2^{n-1}$), with ratios $a_{n+1}/a_n=2$ constant — the **opposite** extreme from Erdős's "$a_{n+1}/a_n\to 1$" challenge.

More generally, any **Sidon-type** sequence whose subset-sums encode subset size will work. For instance:
* Any $A$ with $a_1\ge 1$ and $a_{n+1}>a_1+a_2+\cdots+a_n$ (super-increasing) is admissible: the largest element in a subset sum is determined by $v$, peel and recurse, recovering the subset (and its size). Such $A$ grow at least as fast as $2^n$ in this construction.

## Why polynomial gaps are *not* trivially excluded

A first instinct is to try a pigeonhole: there are $2^N-1$ nonempty subsets of $\{a_1,\dots,a_N\}$, all sums lie in $[1, N\cdot a_N]$, and disjointness across $r$ partitions these sums by subset-size. But **disjointness across $r$ does not impose uniqueness within a fixed $r$**: many distinct $r$-subsets are allowed to share a sum. Concretely, if $a_n\le N^{c}$ for $n\le N$, then
$$\textstyle\sum_{r=1}^{N} |S_r| \;=\; |S_1\sqcup\cdots\sqcup S_N| \;\le\; N\cdot N^{c} \;=\; N^{c+1},$$
which is consistent with $|S_r|$ being only polynomial in $N$ even when there are $\binom{N}{r}$ underlying $r$-subsets. The trivial lower bound $|S_r|\ge N-r+1$ (vary the largest element) gives $\sum_r|S_r|\ge N(N+1)/2$, comfortably below $N^{c+1}$ for any $c\ge 1$.

Conclusion: **a polynomial gap-bound is not ruled out by elementary counting alone**. Whatever obstruction Erdős had in mind is structural, not size-pigeonhole.

## What is actually known (best-effort literature pointer)

Problem #875's entry on erdosproblems.com lists references `[Er98]` and points at #874 (finite version), #876 (a related extension), and the much-broader Sidon-set landscape (#2, #1, #83, #888, #1998, #2000, #39). The OEIS pointers (C124171, B884451, C042214) appear to be auto-extracted ID-style references and were not resolvable to canonical OEIS sequences at the time of this session.

This session does **not** attempt a literature dive — that is the explicit S2 task. The ORIENT-pass goal is to (a) confirm that a working admissible sequence exists (powers of two), (b) record what *fails* to give a quick polynomial-gap obstruction, and (c) hand off three concrete sub-questions to S2.

## Three sub-questions handed to S2

These factor the original problem into pieces that admit *separate* progress:

**(Q1) Slow growth construction.** Does there exist an admissible $A$ with $a_{n+1}/a_n\to 1$? (Erdős's hint suggests "yes, but non-trivial.") Candidates to try: greedy sequences with a slot-based decoder, polynomial perturbations of $\{n^k\}$ for large $k$, or constructions based on positional notations with carry-suppression.

**(Q2) Polynomial-gap impossibility.** Is there a constant $c>0$ such that admissible $\Rightarrow a_{n+1}-a_n>n^{c}$ infinitely often? The cheap counting argument above does *not* prove this. A more refined argument would likely route through Plünnecke–Ruzsa inequalities applied to $|S_r\sqcup S_{r+1}|$ for $r$ near $N/2$, where $|S_r|$ is known to be large by Sidon-style arguments.

**(Q3) Density / asymptotic upper bound.** Quantify the constraint "$\sum_r |S_r|\le N\cdot a_N$" with a *non-trivial* lower bound on $|S_r|$ (e.g. via the Plünnecke–Ruzsa inequality $|rA|\le |A+A|^r/|A|^{r-1}$, or via additive-energy estimates) to derive a genuine upper bound on the density of $A$ in $[1,X]$.

These are *research questions*, not Lean tasks. Lean follows once any sub-question has a concrete declarative target.

## What this session does *not* do

* **No Lean file.** Creating `proofs/Proofs/Erdos875.lean` with an admissibility predicate + the "powers of 2 are admissible" theorem is a reasonable S2 deliverable; deferring it avoids committing prematurely to a Mathlib API choice (e.g. `Set ℕ` vs. `Function.Embedding ℕ ℕ` vs. a `StrictMono` index sequence) before the Q1/Q2 strategy is clearer.
* **No gallery entry yet.** Open Erdős problems with no Lean artifact and no near-term formalization target are not added to `src/data/proofs/` per the gallery's policy of representing only concrete formal contributions.
* **No literature claims.** The "non-trivial Erdős comment" is recorded as a hint, not as a positive existence claim for a slow-growing admissible $A$.

## Next action (S2)

Pick **one** of Q1, Q2, Q3 — most likely Q1 (slow-growth construction), since a positive answer would be a *concrete* admissible sequence definable in Lean and verifiable, whereas Q2/Q3 are quantitative bounds that require additive-combinatorics infrastructure. If a slot-based greedy construction $a_{n+1}=\text{least admissible extension of }a_n$ has a clean recursive description, it becomes a candidate for a Lean-level definition + computable check up to small $n$.

State.md is updated accordingly.

## Deliverables

* `research/problems/erdos-875/session-1-orient.md` — this file.
* `research/problems/erdos-875/state.md` — updated to phase ORIENT-DONE, next phase S2 with explicit sub-question Q1.
* `research/problems/erdos-875/knowledge.md` — updated with the trivial $\{2^{n-1}\}$ existence proof, the "polynomial gaps not trivially excluded" counterexample-to-pigeonhole, and the Q1/Q2/Q3 hand-off.
