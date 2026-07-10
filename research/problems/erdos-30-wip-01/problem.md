# Problem: Complete the Lean Formalization of Erdős Problem #30 (Sidon Sets and h(N))

**Slug**: erdos-30-wip-01
**Created**: 2026-07-09T17:33:20-07:00
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
A \text{ Sidon} \iff \big(a+b = c+d,\ a,b,c,d \in A \implies \{a,b\} = \{c,d\}\big), \qquad h(N) = \max_{A \subseteq \{1,\dots,N\}} |A|, \quad h(N) = N^{1/2} + O_\varepsilon(N^\varepsilon)?
$$

The Erdős–Turán conjecture (OPEN, $\$1000$ prize) asks whether the maximum Sidon-set size $h(N)$ deviates from $\sqrt{N}$ by at most $N^{\varepsilon}$ for every $\varepsilon > 0$.

### Plain Language

The completion task is to strengthen the work-in-progress Lean 4 formalization of Erdős Problem #30 on Sidon sets. A set of integers is *Sidon* (a $B_2$ set) if all of its pairwise sums are distinct; equivalently, the only way $a+b = c+d$ can happen is the trivial one. Writing $h(N)$ for the largest Sidon subset of $\{1,\ldots,N\}$, Erdős and Turán showed $h(N) \leq \sqrt{N} + N^{1/4} + 1$ in 1941, and Singer's projective-plane construction gives $h(N) \geq (1-o(1))\sqrt{N}$. The $\$1000$ conjecture asks whether the error term is actually only $N^{\varepsilon}$ — the exponent $1/4$ has resisted improvement for over eighty years. The current Lean file proves the equivalence of two Sidon characterizations and verifies a small example, but leaves the entire historical progression of bounds and Singer's construction in comments or as axioms. Our goal is to formalize the provable pieces (the Erdős–Turán counting bound in particular) and keep the open conjecture honestly stated.

### Why This Matters

1. **A flagship open Erdős problem**: The Erdős–Turán error-term conjecture is unsolved with a $\$1000$ prize, and the persistence of the $N^{1/4}$ barrier makes an honest formalization a valuable record of a real research frontier.
2. **The counting-argument bound is verifiable**: The classical Erdős–Turán upper bound follows from counting the $\binom{s}{2}$ distinct pairwise sums against the range $\{2,\ldots,2N\}$ — an elementary inequality that Lean can fully check, converting an axiom into a theorem.
3. **Cross-domain infrastructure**: Sidon sets link additive combinatorics, finite geometry (perfect difference sets from $\mathrm{PG}(2,q)$), and coding theory, so verified Sidon machinery in Mathlib has broad reuse.

## Known Results

### What's Already Proven

- Erdős–Turán upper bound — $h(N) \leq \sqrt{N} + N^{1/4} + 1$ via a pairwise-sum counting argument (Erdős–Turán, J. London Math. Soc. 16, 1941).
- Singer's lower bound — perfect difference sets from $\mathrm{PG}(2,q)$ give $h(N) \geq (1-o(1))\sqrt{N}$ (Singer, 1938).
- Refined constants — Lindström (1969) and Balogh–Füredi–Roy (2021)/Carter–Hunter–O'Bryant (2025) improved the coefficient of $N^{1/4}$ but not the exponent.

### What's Still Open

- Whether the $N^{1/4}$ error exponent can be reduced to any $\varepsilon < 1/4$ (the $\$1000$ conjecture), or whether there is a structural barrier.
- Whether the stronger form $h(N) = \sqrt{N} + O(1)$ holds.

### Our Goal

Complete the WIP Lean file `Proofs/Erdos30Problem.lean`: formalize the Erdős–Turán counting upper bound as a genuine theorem (the $\binom{s}{2} \leq 2N - 3$ inequality bounding a Sidon set's size), verify additional small explicit Sidon sets by exhaustive `decide`, and formalize the reduction theorem showing that a single sub-$1/4$ improvement implies the full conjecture. Historical constant refinements (Lindström, BFR, CHO) and Singer's construction that are asserted rather than derived must stay explicitly axiomatized and disclosed; the open Erdős–Turán conjecture must remain a `Prop`, never claimed proved.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-30 | Parent gallery entry (badge wip): defines `IsSidonSet`, `HasDistinctSums`, `sidonNumber`, `Erdos30Conjecture`, and the bound progression, with the equivalence proved but the bounds axiomatized or documented. | Pairwise-sum counting, perfect difference sets, `Finset` case analysis, projective geometry |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Formalize the Erdős–Turán counting inequality directly.
   - Why it might work: The map $(a,b) \mapsto a+b$ on unordered pairs of a Sidon set is injective into $\{2,\ldots,2N\}$, so $\binom{|A|}{2} \leq 2N - 3$; this is a finite counting argument fully within Mathlib's `Finset.card` toolkit.
   - Risk: converting the cardinality inequality into the clean $\sqrt{N} + N^{1/4} + 1$ bound requires careful real-analytic estimates on the quadratic.

2. **Approach B**: Verify explicit Sidon examples and the reduction theorem by decision and monotonicity.
   - Why it might work: Checking $\{1,2,5,10\}$ (or larger optimal sets) is a finite distinctness check; the reduction "$N^{\varepsilon_0}$ dominated by $N^{\varepsilon}$ for $\varepsilon > \varepsilon_0$" is elementary real analysis.
   - Risk: exhaustive checks scale poorly for larger $N$, and the reduction needs asymptotic bookkeeping around $O_\varepsilon$.

### Key Difficulties

- Turning a clean cardinality bound into the stated $\sqrt{N} + N^{1/4}$ form needs `Real.sqrt`/`rpow` estimates that can be fiddly.
- Singer's construction and the modern constant improvements rest on finite-geometry and probabilistic arguments that are out of scope to fully formalize.

### What Would a Proof Need?

- Key lemma 1: injectivity of the pairwise-sum map on a Sidon set, giving $\binom{|A|}{2} \leq 2N - 3$.
- Key lemma 2: the reduction theorem relating a single $\varepsilon < 1/4$ improvement to the full $O_\varepsilon(N^\varepsilon)$ conjecture.
- Technical requirements: `Finset.card`, `Real.sqrt`/`Real.rpow`, and a decidable Sidon predicate for finite examples.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The core Erdős–Turán upper bound is an elementary counting argument that is genuinely formalizable, so real progress toward `verified` is achievable.
- The open conjecture itself and Singer's geometric construction are beyond scope, but they cleanly remain axiomatized.
- Mathlib provides `Finset` cardinality, real powers, and square roots — exactly the tools the counting bound needs.

**Estimated Effort**:
- Exploration: 1-2 days
- If tractable: 1-2 weeks for the counting bound, examples, and reduction theorem
- If hard: unknown for any improvement to the $N^{1/4}$ exponent

## References

### Papers
- P. Erdős and P. Turán, "On a problem of Sidon in additive number theory, and on some related problems", J. London Math. Soc. 16 (1941), 212–215 — the foundational upper bound.
- B. Lindström, "An inequality for B_2-sequences", J. Combin. Theory 6 (1969), 211–212 — sharpened constant.
- J. Cilleruelo, "Infinite Sidon sets", Adv. Math. 225 (2010), 2786–2803 — dense infinite Sidon constructions.

### Online Resources
- https://erdosproblems.com/30 — canonical statement, open status, and $\$1000$ prize.
- https://www.combinatorics.org/ojs/index.php/eljc/article/view/DS11 — O'Bryant's annotated bibliography of Sidon-set results.

### Mathlib
- `Mathlib.Combinatorics.Additive.Behrend` — additive-combinatorics scaffolding and `Finset` sumset lemmas.
- `Mathlib.Analysis.SpecialFunctions.Pow.Real` — `Real.rpow` and `Real.sqrt` for the $\sqrt{N} + N^{1/4}$ estimates.

## Metadata

```yaml
tags:
  - erdos
  - number-theory
  - additive-combinatorics
  - sidon-sets
  - b2-sequences
  - open-problem
related_proofs:
  - erdos-30
difficulty: medium
source: proof-suggestion
created: 2026-07-09T17:33:20-07:00
```

**Significance**: 8/10
**Tractability**: 6/10
