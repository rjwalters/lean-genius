# Problem: Erdős-Hajnal Connectivity Question at ℵ₂ and Higher Alephs

**Slug**: erdos-1067-oq-03
**Created**: 2026-07-09T15:40:18-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\forall \kappa \in \{\aleph_2, \aleph_3, \dots\}: \Big(\chi(G) = \kappa \implies \exists H \subseteq G,\ H \text{ infinitely connected} \wedge \chi(H) = \kappa\Big) \stackrel{?}{=} \text{FALSE}
$$

The gallery proof of Erdős Problem #1067 established that at $\kappa = \aleph_1$ the universal implication is **false** (Soukup 2015, Bowler-Pitz 2024): there exist graphs with $\chi(G) = \aleph_1$ whose every infinitely connected subgraph has chromatic number strictly below $\aleph_1$. The present problem asks whether the same negative answer holds when $\aleph_1$ is replaced by $\aleph_2$ or any higher aleph $\aleph_\alpha$ ($\alpha \ge 2$), and whether the ZFC-independence seen in the $|V(G)| = \aleph_1$ restriction reappears at these larger cardinals.

### Plain Language

A graph is *infinitely connected* if between any two vertices there are infinitely many internally disjoint paths (no finite set of vertices can separate them). The chromatic number $\chi(G)$ measures how many colors are needed so adjacent vertices differ. Erdős and Hajnal asked whether a graph that genuinely needs $\aleph_1$ colors must hide inside it a highly-connected piece that still needs $\aleph_1$ colors. The answer at $\aleph_1$ turned out to be no. This problem asks the next natural question: if a graph needs $\aleph_2$ colors (or $\aleph_3$, or any higher uncountable cardinal), is it still possible to build a counterexample where the "hard-to-color core" avoids being infinitely connected? And does the phenomenon where the answer flips depending on which set-theoretic axioms you assume — seen for the $\aleph_1$-vertex variant — continue to appear at these larger scales?

### Why This Matters

Resolving this would clarify whether the decoupling of chromatic number from connectivity is a special feature of $\aleph_1$ or a general phenomenon of uncountable chromatic combinatorics. If the negative answer lifts uniformly to all $\aleph_\alpha$, it strengthens the structural picture that "chromatic difficulty" can always be distributed across thin, tree-like regions regardless of scale. If the independence phenomenon persists (or intensifies) at $\aleph_2$, it would tie the question to large-cardinal and forcing hierarchies, connecting Erdős-style combinatorics to the deepest parts of set theory. The Soukup and Bowler-Pitz constructions are cardinal-parametrized, so understanding which parts survive successor and limit cardinals is a concrete test of how robust those techniques are.

## Known Results

### What's Already Proven

- Erdős-Hajnal question at $\aleph_1$ is **false** in ZFC (Soukup 2015) — axiomatized as `soukup_counterexample_2015` in `Proofs/Erdos1067Problem.lean`
- Elementary counterexample at $\aleph_1$ (Bowler-Pitz 2024) — axiomatized as `bowler_pitz_counterexample_2024` in the same file
- Consistency of a counterexample via forcing, plus ZFC-independence for the $|V(G)| = \aleph_1$ restriction (Komjáth 2013) — `Combinatorica`
- Edge-connectivity analogue at $\aleph_1$ is also false (Thomassen 2017) — `Journal of Graph Theory`

### What's Still Open

- Whether $\chi(G) = \aleph_2$ forces an infinitely connected subgraph with $\chi = \aleph_2$ (no published ZFC counterexample known at $\aleph_2$)
- Whether the ZFC-independence of the vertex-restricted variant reappears when $|V(G)| = \aleph_2$ or $|V(G)| = \aleph_\alpha$
- Whether Soukup's ladder-tree construction generalizes to successor cardinals $\aleph_{\alpha+1}$ and to limit cardinals such as $\aleph_\omega$
- Whether large-cardinal hypotheses change the answer at sufficiently high alephs

### Our Goal

Formalize the *statement* of the generalized Erdős-Hajnal question at arbitrary aleph $\kappa$ (parametrized by an ordinal $\alpha$), building on the existing `ErdosHajnalQuestion` definition so that the $\aleph_1$ case is recovered by specialization. Establish the axiomatized negative answer at $\aleph_2$ conditional on the appropriate construction, and record the independence-versus-ZFC dichotomy as separate hypotheses. The concrete scope is a Lean scaffold that (a) generalizes `hasAleph1ChromaticNumber` to `hasChromaticNumber κ`, and (b) states the higher-aleph question as a theorem whose proof is deferred to axioms mirroring the $\aleph_1$ structure.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1067 | Direct parent: this generalizes its $\aleph_1$ result to higher alephs | Cardinal chromatic number, infinite connectivity, axiomatized counterexamples, `push_neg` |
| erdos-1068 | Countable-connectivity companion from the same Soukup 2015 paper | Infinite vertex connectivity, uncountable $\chi$ |
| erdos-62 | Common-subgraph structure of graphs with $\chi = \aleph_1$ | Uncountable chromatic graphs, shared subgraph existence |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Cardinal-parametrize Soukup's ladder-tree construction**: Rework Soukup's construction with $\aleph_2$ (or $\aleph_\alpha$) replacing $\aleph_1$ throughout, using trees of height/width scaled to $\kappa$.
   - Why it might work: The construction's chromatic bottleneck comes from global tree structure, which is cardinal-agnostic in principle.
   - Risk: Successor-cardinal combinatorics (e.g. the tree property, $\square_\kappa$ principles) may obstruct the coloring argument at $\aleph_2$, making the "locally countably colorable" step fail.

2. **Approach B — Reduce higher alephs to $\aleph_1$ via elementary submodels or partition calculus**: Try to derive a counterexample at $\aleph_2$ from the $\aleph_1$ counterexample by a lifting / product argument.
   - Why it might work: Partition relations $\kappa \to (\kappa)^2_\lambda$ style transfers sometimes carry combinatorial obstructions upward.
   - Risk: Chromatic number does not behave multiplicatively under natural products; a naive lift may only give $\chi = \aleph_1$, not $\aleph_2$.

### Key Difficulties

- Successor cardinals above $\aleph_1$ carry extra combinatorial structure (stationary reflection, square principles) that can either enable or destroy the construction, and these are themselves independence-sensitive.
- Mathlib has cardinal arithmetic (`Cardinal.aleph`) but essentially no infinite-graph coloring or infinite Menger/connectivity theory, so most supporting infrastructure must be built or axiomatized.

### What Would a Proof Need?

- Key lemma 1: A cardinal-parametrized chromatic-number predicate `hasChromaticNumber κ G` generalizing `hasAleph1ChromaticNumber`, with the $\aleph_1$ instance definitionally recovered.
- Key lemma 2: A statement `ErdosHajnalQuestionAt κ` and, conditional on axioms, its refutation at $\kappa = \aleph_2$ mirroring `erdos_1067_answer`.
- Technical requirements: Infinite Menger equivalence for the parametrized `InfinitelyConnected` predicate; a means to record ZFC-independence hypotheses as explicit assumptions rather than proved facts.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The mathematical question is genuinely open at $\aleph_2$; no known ZFC counterexample exists, and the independence behavior is unresolved, so a full resolution is a research-level set-theory problem.
- The *formalization of the statement* and an axiomatized scaffold are tractable, following the established pattern of the erdos-1067 gallery entry.
- Similar axiomatize-the-deep-result approach already succeeded at $\aleph_1$ (Soukup, Bowler-Pitz axioms), giving a clear template.
- Mathlib provides `Cardinal.aleph` and `SimpleGraph` but no infinite chromatic/connectivity theory, so unaxiomatized progress is limited.

**Estimated Effort**:
- Exploration: 2-4 days
- If tractable (statement + axiomatized scaffold): 1-2 weeks
- If hard (unaxiomatized construction or independence result): unknown / open research

## References

### Papers
- Lajos Soukup, "Infinite graphs with no odd cycles of a given length", European Journal of Combinatorics, 2015 — ZFC counterexample at $\aleph_1$; the construction to attempt to lift.
- Nathan Bowler, Steffen Pitz, "A simpler proof of the Erdős-Hajnal conjecture for forests", arXiv, 2024 — elementary $\aleph_1$ construction, a candidate for cleaner cardinal parametrization.
- Péter Komjáth, "A note on uncountably chromatic graphs", Combinatorica, 2013 — ZFC-independence of the vertex-restricted variant; template for higher-aleph independence.
- Paul Erdős, András Hajnal, "On chromatic number of graphs and set-systems", Acta Mathematica Hungarica, 1966 — origin of the question and uncountable-chromatic program.

### Online Resources
- https://erdosproblems.com/1067 — canonical statement and status of Erdős Problem #1067.

### Mathlib
- `Mathlib.SetTheory.Cardinal.Ordinal` — provides `Cardinal.aleph` for $\aleph_\alpha$ indexed by ordinals, needed to parametrize the question.
- `Mathlib.Combinatorics.SimpleGraph.Basic` — `SimpleGraph` structure underlying the graph, subgraph, and coloring definitions.

## Metadata

```yaml
tags:
  - set-theory
  - graph-theory
  - chromatic-number
  - infinite-graphs
  - connectivity
related_proofs:
  - erdos-1067
  - erdos-1068
difficulty: high
source: proof-suggestion
created: 2026-07-09T15:40:18-07:00
```
