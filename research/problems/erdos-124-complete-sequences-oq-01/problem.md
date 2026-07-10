# Problem: Erdős #124 — The Strong Version Excluding the Power d^0 = 1

**Slug**: erdos-124-complete-sequences-oq-01
**Created**: 2026-07-09T17:03:06-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\begin{aligned}
&\text{Given integers } d_1, \ldots, d_k \ge 2, \text{ consider the set of powers}\\
&\quad S = \{\, d_i^{\,e} : 1 \le i \le k,\; e \ge 1 \,\}
\quad\text{(the exponent } e=0, \text{ i.e. the value } 1, \text{ is excluded).}\\[4pt]
&\textbf{Question.}\ \text{Under which arithmetic conditions on } (d_1,\ldots,d_k) \text{ is } S\\
&\quad\textit{complete}, \text{ i.e. every sufficiently large } n\in\mathbb{N} \text{ is a subset sum of } S?\\[4pt]
&\text{Equivalently: for which } (d_1,\ldots,d_k) \text{ can every large } n \text{ be written}\\
&\quad n = \sum_{i=1}^{k} a_i, \qquad a_i = \sum_{e\ge 1} \varepsilon_{i,e}\, d_i^{\,e},\quad \varepsilon_{i,e}\in\{0,1\},\\
&\text{using only 0/1 digits in each base } d_i \textit{ and no constant term } \varepsilon_{i,0}?
\end{aligned}
$$

### Plain Language

The weak version of Erdős #124 (now solved) asks whether every natural number can be written as a sum $\sum a_i$, where each $a_i$ uses only the digits 0 and 1 in base $d_i$, whenever $\sum_i \frac{1}{d_i-1} \ge 1$. In the weak version each base is allowed to contribute the digit-value $1 = d_i^0$, which makes small numbers easy to represent. The **strong version** removes this crutch: the power $d_i^0 = 1$ is *not* available, so the building blocks are only $d_i, d_i^2, d_i^3, \ldots$. The open question is to determine exactly which tuples $(d_1,\ldots,d_k)$ still make the resulting set of powers *complete* — able to represent all sufficiently large integers as subset sums — once the value 1 is forbidden.

### Why This Matters

Erdős #124 was historically significant as the first open conjecture solved autonomously by an AI system (Harmonic's Aristotle, November 2025). But the solved statement is the *weak* form. Erdős himself reformulated the problem twice in 1997, introducing ambiguity, and one of the surviving formulations — the strong version excluding $d^0 = 1$ — remains open. Resolving it would (a) complete the historical record of what Erdős actually asked, (b) sharpen the theory of *complete sequences* and *subset-sum representability* by pinning down the exact threshold when the trivial term is removed, and (c) test whether Brown's-criterion machinery is robust to the loss of the anchoring value 1, which is precisely the hypothesis that makes the criterion apply.

## Known Results

### What's Already Proven

- **Erdős #124 (weak version)** — solved by Harmonic Aristotle (2025), formalized in this gallery as `erdos-124-complete-sequences`. If $\sum_{i=1}^k \frac{1}{d_i - 1} \ge 1$ then every $n$ is a subset sum of $\{d_i^e : e \ge 0\}$ (the term $d_i^0 = 1$ **is** allowed).
- **Brown's criterion** — a non-decreasing sequence $u_1 \le u_2 \le \cdots$ with $u_1 = 1$ is complete iff $u_{n+1} \le 1 + \sum_{j\le n} u_j$ for all $n$. This is the engine behind the weak solution; see `Proofs/Erdos124CompleteSequences.lean`.
- **Cassels / classical completeness theory** — general criteria for a sequence of positive integers to represent all large integers as subset sums (Cassels, 1960), which apply when a sequence has bounded gap ratios.

### What's Still Open

- The exact necessary-and-sufficient condition on $(d_1,\ldots,d_k)$ for completeness when $d^0 = 1$ is excluded from every base.
- Whether the reciprocal threshold $\sum \frac{1}{d_i-1} \ge 1$ must be *strengthened* (e.g. to a strict inequality, or supplemented by a gcd/coprimality condition on the $d_i$) once the value 1 is removed. In particular, the smallest few integers (which the weak version handles trivially via $1 = d_i^0$) may become genuinely unrepresentable, forcing a "sufficiently large" caveat and/or extra hypotheses.
- Whether a greedy-power sequence that omits all $d_i^0$ still satisfies Brown's small-gap inequality, or whether the loss of the leading $u_1 = 1$ breaks the criterion at the base case.

### Our Goal

Formalize the strong-version statement precisely, and either (i) prove a clean sufficient condition — e.g. that $\sum \frac{1}{d_i-1} \ge 1$ together with $\gcd(d_1,\ldots,d_k) = 1$ implies every *sufficiently large* $n$ is representable without the $d_i^0$ terms — or (ii) exhibit an explicit family of counterexamples showing the weak-version threshold is genuinely insufficient once 1 is excluded. Even a rigorous reduction of the strong version to a Brown-criterion statement about the gap-shifted sequence would be a valuable, checkable contribution.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-124-complete-sequences | Parent proof: solves the weak version (with $d^0=1$ allowed); the strong version is its natural sharpening | Brown's criterion, greedy power sequence, digit decomposition |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Shifted Brown's criterion**: Model the strong version as completeness of the multiset $S = \{d_i^e : e \ge 1\}$, sort it into a non-decreasing sequence $(u_n)$, and check Brown's gap inequality $u_{n+1} \le 1 + \sum_{j\le n} u_j$. The weak proof anchors on $u_1 = 1$; here the smallest element is $\min_i d_i \ge 2$, so the base case of the induction fails and completeness can only hold "eventually." Prove instead the *eventual* form: there is $N_0$ such that all $n \ge N_0$ are subset sums, by showing the gap condition holds for all sufficiently large indices.
   - Why it might work: the reciprocal condition $\sum 1/(d_i-1) \ge 1$ is exactly what controls the growth rate of the greedy power sequence, and that argument is index-tail insensitive.
   - Risk: the small-$n$ gap between $1$ and $\min_i d_i$ may propagate, leaving an unbounded set of exceptional residues unless a gcd condition is added.

2. **Approach B — gcd / coprimality supplement**: Conjecture and prove that $\sum \frac{1}{d_i-1} \ge 1$ **and** $\gcd(d_1,\ldots,d_k)=1$ jointly suffice for eventual completeness. If $g = \gcd > 1$, only multiples of $g$ near the low end are representable, giving an immediate obstruction; coprimality removes it via a Chicken-McNugget / numerical-semigroup argument on the residues.
   - Why it might work: numerical-semigroup (Frobenius) theory precisely governs which residues are eventually hit by nonnegative combinations, matching the "sufficiently large" phenomenon.
   - Risk: combining a Frobenius-style residue argument with the analytic Brown growth bound is delicate; the two must agree on the same threshold $N_0$.

### Key Difficulties

- Loss of the anchor $u_1 = 1$ invalidates the induction base of Brown's criterion, so completeness (all $n$) must be weakened to eventual completeness (all large $n$), changing the theorem shape.
- Determining whether the *same* reciprocal threshold suffices, or whether it must be strengthened / paired with a gcd condition — this is the actual open mathematical content.
- Small cases behave irregularly (finitely many exceptional $n$), which is hard to formalize cleanly without an explicit, provable bound $N_0$.

### What Would a Proof Need?

- Key lemma 1: a growth/gap estimate showing the sorted power sequence $\{d_i^e : e\ge1\}$ satisfies Brown's inequality for all indices $\ge$ some explicit $N_0$, given $\sum 1/(d_i-1)\ge 1$.
- Key lemma 2: a residue-coverage lemma (numerical-semigroup style) guaranteeing that when $\gcd(d_i)=1$ every residue class is eventually hit, closing the finitely-many small exceptions.
- Technical requirements: a formalized "eventual completeness" predicate, an explicit exceptional bound $N_0$, and reuse of the digit-decomposition lemmas from the parent Lean file.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The problem is a genuinely open reformulation of an Erdős problem; the correct sufficient condition is not settled in the literature, so it is research-grade rather than a routine formalization.
- The parent weak version was itself only solved in 2025 (by AI), indicating the surrounding theory is subtle.
- Positive signs: the tools (Brown's criterion, numerical semigroups, digit decomposition) all exist in usable form, and Mathlib has `Nat.digits`, finite-sum, and gcd infrastructure, so an *eventual-completeness under gcd = 1* result may be within reach even if the full characterization is not.

**Estimated Effort**:
- Exploration: 2–4 days to nail the exact statement and small-case behavior.
- If tractable: 2–4 weeks for a sufficient-condition theorem with an explicit exceptional bound.
- If hard: unknown (full necessary-and-sufficient characterization).

## References

### Papers
- S. A. Burr, P. Erdős, R. L. Graham, W.-C. W. Li, "Complete sequences of sets of integer powers," *Acta Arithmetica* 77 (1996), 133–138 — the original source of Problem #124.
- P. Erdős, "Some of my new and almost new problems and results in combinatorial number theory," (1997) — the reformulations that introduced the weak/strong ambiguity.
- J. W. S. Cassels, "On the representation of integers as the sums of distinct summands taken from a fixed set," *Acta Sci. Math. Szeged* 21 (1960), 111–124 — classical completeness criteria.

### Online Resources
- https://www.erdosproblems.com/124 — canonical statement and status of Erdős Problem #124.
- https://harmonic.fun — Harmonic's Aristotle system that solved the weak version.

### Mathlib
- `Mathlib.Data.Nat.Digits` — digit representation in an arbitrary base; underpins the 0/1-digit condition.
- `Mathlib.Algebra.BigOperators.Group.Finset` — finite sums (`Finset.sum`) for subset-sum representations.
- `Mathlib.Order.Filter.Basic` — `Filter.Eventually`, for phrasing "every sufficiently large $n$".
- `Mathlib.RingTheory.Int.Basic` / `Mathlib.Algebra.GCDMonoid.Basic` — gcd machinery for the coprimality supplement.

## Metadata

```yaml
tags:
  - number-theory
  - combinatorics
  - erdos
  - ai-solved
  - complete-sequences
related_proofs:
  - erdos-124-complete-sequences
difficulty: high
source: proof-suggestion
created: 2026-07-09T17:03:06-07:00
```
