# Problem: Erdős–Turán Upper Bound for Sidon Sets

**Slug**: erdos-340-greedy-sidon-oq-02
**Created**: 2026-06-17
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
A \subseteq \{1,\dots,N\} \text{ Sidon} \;\Longrightarrow\; |A| \le \sqrt{N} + O\!\left(N^{1/4}\right).
$$

More precisely, the classical Erdős–Turán bound (1941) states that a Sidon set
$A \subseteq \{1,\dots,N\}$ (all pairwise sums $a+b$ distinct) satisfies
$|A| \le \sqrt{N} + N^{1/4} + 1$.

### Plain Language

A *Sidon set* is a set of integers in which all pairwise sums are distinct
(equivalently, all positive differences are distinct). We want to formalize the
tight upper bound on how large such a set inside $\{1,\dots,N\}$ can be: roughly
$\sqrt{N}$. The bound is proved by a counting (double-counting) argument on the
differences $a - b$ with $a > b$: there are $\binom{|A|}{2}$ such differences,
they are all distinct, and they all lie in $\{1,\dots,N-1\}$, which already gives
$\binom{|A|}{2} \le N-1$ and hence $|A| \lesssim \sqrt{2N}$. The sharper
$\sqrt{N} + O(N^{1/4})$ comes from counting differences in a window and averaging
over shifts.

### Why This Matters

The Erdős–Turán theorem is the foundational upper bound of Sidon-set theory and
the matching companion to the construction lower bounds (Singer / Erdős–Turán
$\approx \sqrt{N}$). Formalizing it completes the two-sided picture for Erdős
Problem #340 in the gallery, where the lower-bound infrastructure and difference
injectivity are already proven. It also supplies a reusable counting lemma for
other extremal additive-combinatorics entries.

## Known Results

### What's Already Proven

- Sidon closure, difference injectivity, and the basic Sidon library — `proofs/Proofs/Erdos340GreedySidon.lean` (537 lines, 0 sorries; gallery `erdos-340-greedy-sidon`)
- The weak counting bound $\binom{|A|}{2} \le N-1$ follows directly from difference injectivity already in the library
- Singer-type / greedy lower-bound constructions giving Sidon sets of size $\approx \sqrt{N}$ (companion open questions oq-01/oq-03)

### What's Still Open

- The sharp second-order term $O(N^{1/4})$ via windowed difference counting
- A fully formal statement and proof of $|A| \le \sqrt{N} + N^{1/4} + 1$

### Our Goal

Formalize, in Lean 4 over Mathlib, the Erdős–Turán upper bound. A first milestone
is the clean $|A|(|A|-1) \le 2(N-1)$ form (immediate from existing difference
injectivity), then strengthen to $\sqrt{N} + O(N^{1/4})$ using the shifted-window
averaging argument.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-340-greedy-sidon | Parent: provides the Sidon set definition, difference injectivity, and counting scaffolding | Finset cardinality, injective difference map |
| Mathlib `Finset.Sidon` (if present at pin) | Canonical Sidon predicate and API | additive combinatorics |

## Initial Thoughts

### Potential Approaches

1. **Approach A — direct difference counting**: Map $A \times A$ restricted to
   $a > b$ injectively into $\{1,\dots,N-1\}$ via $(a,b) \mapsto a-b$. Cardinality
   gives $\binom{|A|}{2} \le N-1$, i.e. $|A| \le \tfrac{1+\sqrt{8N-7}}{2}$.
   - Why it might work: difference injectivity is already a proven lemma in the parent file.
   - Risk: only yields the $\sqrt{2N}$ constant, not the sharp $\sqrt{N}$.

2. **Approach B — windowed/shifted counting (Erdős–Turán)**: Count differences
   $a-b \in (0, u]$ for a window length $u$, sum over the $N$ shifts of the window,
   and optimize $u \approx N^{3/4}$ to obtain $\sqrt{N} + O(N^{1/4})$.
   - Why it might work: it is the textbook proof; each step is elementary counting.
   - Risk: the averaging/optimization bookkeeping is fiddly in Lean (real-valued
     estimates, `Nat`/`Real` casts).

### Key Difficulties

- Real-valued second-order estimates and casts between `Nat` and `Real`
- Choosing and formalizing the optimal window length $u$
- Reusing vs. re-deriving the difference-injectivity lemma from the parent module

### What Would a Proof Need?

- Key lemma 1: injectivity of $(a,b) \mapsto a-b$ on $\{(a,b) : a,b \in A, a>b\}$ (already available)
- Key lemma 2: window-shift double count $\sum_u |\{(a,b): 0 < a-b \le u\}|$
- Technical requirements: `Finset.card_le_card_of_injOn`, real arithmetic, `Nat.sqrt`/`Real.sqrt` bridging

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The weak form is essentially immediate from existing lemmas (low-risk first win).
- The sharp form is a well-documented classical argument with no missing Mathlib prerequisites.
- Similar counting/extremal bounds have been formalized in the gallery.

**Estimated Effort**:
- Exploration: hours
- If tractable (weak form + sharp form): days
- If hard (full $O(N^{1/4})$ with tight constant): up to a week

## References

### Papers
- P. Erdős and P. Turán, "On a problem of Sidon in additive number theory, and on some related problems", J. London Math. Soc. 16 (1941), 212–215 — original upper bound.
- H. Halberstam and K. F. Roth, *Sequences*, Ch. II — textbook treatment of Sidon (B₂) sets.

### Online Resources
- https://www.erdosproblems.com/340 — Erdős Problem #340 statement and references.

### Mathlib
- `Mathlib.Combinatorics.Additive` / `Finset.Sidon` — Sidon predicate and basic API (verify availability at pin).
- `Finset.card_le_card_of_injOn` — counting via injection.

## Metadata

```yaml
tags:
  - combinatorics
  - additive-combinatorics
  - sidon-sets
  - extremal
related_proofs:
  - erdos-340-greedy-sidon
difficulty: medium
source: proof-suggestion
created: 2026-06-17
```
