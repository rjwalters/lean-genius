# Problem: Abundance of Good Sets for Non-Uniform, Weight-Bounded Families (Erdős #1027 Extension)

**Slug**: erdos-1027-oq-04
**Created**: 2026-07-09T17:03:07-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\forall c > 0,\ \exists \delta = \delta(c) > 0 : \quad
\Bigl(\sum_{A \in \mathcal{F}} 2^{-|A|} \le c \ \wedge\ \min_{A \in \mathcal{F}} |A| \to \infty\Bigr)
\ \Longrightarrow\
\bigl|\{\, B \subseteq X : (\forall A \in \mathcal{F})\ B \cap A \ne \emptyset \ \wedge\ A \not\subseteq B \,\}\bigr|
\ \ge\ \delta \cdot 2^{|X|},
$$

where $X = \bigcup_{A \in \mathcal{F}} A$ and $\mathcal{F}$ is a finite family of finite sets of *varying* sizes.

### Plain Language

Erdős Problem #1027 (solved by Koishi Chan) shows that for a family of at most $c \cdot 2^n$ sets **all of the same size $n$**, a constant fraction $\delta(c)$ of all subsets of the ground set $X$ are "good" — they hit every set in the family but contain none of them. This extension asks whether the same abundance survives when the sets have **different sizes**. The natural way to bound a non-uniform family is by its total *weight* $\sum_{A \in \mathcal{F}} 2^{-|A|}$, the same quantity that controls the union bound in Erdős's classical Property B argument (a set of size $s$ is monochromatic under a random 2-coloring with probability $2^{1-s}$). The question: if this weight is at most $c$, must a constant fraction $\delta(c)$ of subsets still be good?

### Why This Matters

The weight $\sum_A 2^{-|A|}$ is the *right* invariant for Property B: Erdős's 1963 union-bound theorem says $\sum_A 2^{1-|A|} < 1$ already guarantees 2-colorability, regardless of set sizes. Replacing the uniform cardinality constraint $|\mathcal{F}| \le c\,2^n$ by the weight constraint $\sum_A 2^{-|A|} \le c$ recovers the uniform case exactly (when all $|A| = n$, the weight is $|\mathcal{F}|\,2^{-n} \le c$) while covering genuinely non-uniform families. A positive answer would show that #1027's supersaturation phenomenon is a statement about *weight*, not cardinality — placing it alongside the Lovász Local Lemma and the hypergraph container method as weight-driven counting results. A negative answer would isolate uniformity as essential, which would itself be informative.

## Known Results

### What's Already Proven

- **Erdős #1027 (uniform case)** — Koishi Chan proved that a family of at most $c\,2^n$ sets of common size $n$ has $\ge \delta(c)\,2^{|X|}$ good sets. Formalized in the gallery as `erdos-1027` (`Proofs/Erdos1027Problem.lean`), with the abundance statement `Erdos1027Statement` axiomatized as `erdos_1027_solution` and Property B / 2-colorability established sorry-free.
- **Erdős's classical Property B bound (1963)** — If $\sum_{A \in \mathcal{F}} 2^{1-|A|} < 1$ (in particular if $|\mathcal{F}| < 2^{t-1}$ and every $|A| \ge t$), then $\mathcal{F}$ is 2-colorable, i.e. has *at least one* good set. This is `erdos_classical_bound` in the parent file and already handles non-uniform families for the *existential* question. The tightness construction (Erdős: $2^{t-1}$ sets of size $t$) is uniform.
- **Property B $\iff$ 2-colorability** — `propertyB_implies_2colorable` and `coloring_implies_propertyB` (parent file, sorry-free): good sets are exactly the proper 2-colorings, via $B = f^{-1}(\text{true})$.

### What's Still Open

- The abundance (constant-fraction) statement for **non-uniform** families under the weight bound $\sum_A 2^{-|A|} \le c$ — this problem.
- Whether the correct constant is $\delta(c) \asymp e^{-2c}$ (the probabilistic heuristic value) in the non-uniform regime, and whether the answer degrades if the minimum set size is *not* forced to grow.
- The analogous quantitative strengthening of Erdős #901 (Property B for bounded families) in the weighted setting.

### Our Goal

Establish the weighted abundance bound above, or find a counterexample. A tractable first milestone: prove the **union-bound abundance lemma** — if $\sum_{A \in \mathcal{F}} 2^{1-|A|} \le \tfrac12$ then a *random* $B \subseteq X$ is good with probability $\ge \tfrac12$, hence at least $2^{|X|-1}$ good sets exist. This already gives non-uniform abundance in the *small-weight* regime and is fully formalizable in Mathlib.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1027 | Parent problem; this is the non-uniform generalization of its abundance statement | Property B, good-set counting, probabilistic/union-bound, axiomatized abundance |
| erdos-1027 (Section VII, `erdos_classical_bound`) | Provides the weight-driven union bound already handling varying sizes existentially | Injection counting of monochromatic subsets, probabilistic method |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Weighted first-moment / union bound**: For a uniformly random $B \subseteq X$, $\Pr[B \cap A = \emptyset] = \Pr[A \subseteq B] = 2^{-|A|}$. By the union bound, $\Pr[B \text{ not good}] \le \sum_A 2 \cdot 2^{-|A|} = 2\sum_A 2^{-|A|} \le 2c$. This is only useful when $c < \tfrac12$, but in that range it *immediately* proves $\ge (1-2c)\,2^{|X|}$ good sets, non-uniform and clean.
   - Why it might work: the size-independence of $2^{-|A|}$ makes the bound purely weight-driven; no uniformity is used.
   - Risk: fails for $c \ge \tfrac12$; needs amplification to reach general $c$.

2. **Approach B — Local Lemma / amplification for large $c$**: Model "$B$ is bad" as a union of dependent events (one per set $A$, split into "misses $A$" and "contains $A$"). Each event has probability $2^{-|A|}$ and depends only on the coordinates in $A$; two events are independent if their sets are disjoint. The symmetric Lovász Local Lemma gives a positive probability, and the *lopsided/algorithmic* LLL (Moser–Tardos) can be pushed to a constant-fraction count by counting the outputs of the resampling process, exactly as in the uniform proof of #1027.
   - Why it might work: LLL is naturally weighted (condition is on $e \cdot p \cdot (d+1) \le 1$), and the dependency degree is controlled by how many large sets share an element.
   - Risk: the dependency degree can be large if many small sets overlap; the constant $\delta(c)$ may then depend on the minimum size, motivating the $\min|A| \to \infty$ hypothesis.

### Key Difficulties

- Reducing general $c$ to the small-weight regime: the uniform proof amplifies via "free" (non-critical) elements; with varying sizes, small sets create many critical elements and shrink the free set.
- Handling families with many tiny sets: a single element $x$ can be forced (a set $\{x\}$ forces $x \notin B$ to miss it and $x \in$ every $B$ to... ), so pathological non-uniform families may need the $\min|A|\to\infty$ (or a minimum-size) hypothesis to be meaningful.
- Making the container/entropy count uniform in the size distribution rather than in a single $n$.

### What Would a Proof Need?

- Key lemma 1: **Weighted union bound** — $\Pr[B\text{ not good}] \le 2\sum_A 2^{-|A|}$ (elementary; formalizable now).
- Key lemma 2: **Weighted amplification** — from one good $B$, toggling non-critical coordinates yields $2^{|X| - g(c)}$ good sets, with $g(c)$ depending only on the weight.
- Technical requirements: a Mathlib-friendly probability space on `Finset X` (uniform measure), or a purely counting reformulation; symmetric LLL or a bespoke second-moment argument; possibly `Finset.exists_...` counting of complement functions as used in `card_constOn_le`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The small-weight regime ($c < \tfrac12$) is genuinely tractable — it is a one-line union bound and fully formalizable in Mathlib today, giving a real, publishable partial result.
- The general case reduces to whether the uniform amplification argument of #1027 is weight-driven; since Erdős's classical bound (`erdos_classical_bound`) is *already* weight-based and non-uniform, there is strong evidence the phenomenon persists.
- Similar quantitative Property B results (supersaturation, container method) are known to be robust to non-uniformity, so a counterexample seems unlikely for $\min|A|\to\infty$; the main risk is pinning the correct constant.

**Estimated Effort**:
- Exploration: 1-2 days (formalize the weighted union bound; test small non-uniform examples).
- If tractable: 1-2 weeks (amplification lemma for general $c$).
- If hard: unknown (the sharp constant / dropping the min-size hypothesis).

## References

### Papers
- P. Erdős, "On a combinatorial problem," *Nordisk Mat. Tidskr.* 11 (1963), 5–10 — the classical $2^{1-|A|}$ union-bound Property B theorem, already weight-based.
- P. Erdős and L. Lovász, "Problems and results on 3-chromatic hypergraphs and some related questions," *Infinite and Finite Sets* (1975) — the Lovász Local Lemma and its Property B application.
- J. Balogh, R. Morris, W. Samotij, "Independent sets in hypergraphs," *J. Amer. Math. Soc.* 28 (2015) — the container method for counting independent sets (good sets are independent sets of the "bad" hypergraph).
- D. Saxton, A. Thomason, "Hypergraph containers," *Invent. Math.* 201 (2015) — companion container framework.

### Online Resources
- https://erdosproblems.com/1027 — the parent problem statement and Koishi Chan's affirmative resolution.
- https://erdosproblems.com/901 — the closely related bounded-family Property B question.

### Mathlib
- `Mathlib.Combinatorics.SetFamily.Shadow` — set-family combinatorics infrastructure over `Finset (Finset α)`.
- `Mathlib.Probability.ProbabilityMassFunction.Basic` — uniform distribution on a finite type for the random-subset argument.
- `Mathlib.Analysis.SpecialFunctions.Log.Basic` and `Mathlib.Analysis.SpecialFunctions.Pow.Real` — for the $e^{-2c}$ asymptotics of the abundance constant.
- `Mathlib.Combinatorics.Enumerative.DoubleCounting` — double-counting / injection tools mirroring `card_constOn_le`.

## Metadata

```yaml
tags:
  - combinatorics
  - set-families
  - erdos
  - property-b
  - 2-colorable
related_proofs:
  - erdos-1027
difficulty: medium
source: gallery-gap
created: 2026-07-09T17:03:07-07:00
```
