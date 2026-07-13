# Problem: Complete the Lean Formalization of Erdős #85 (Monotone Minimum-Degree Threshold for 4-Cycles)

**Slug**: erdos-85-wip-01
**Created**: 2026-07-09T17:33:20-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
f(n) = \min \{\, d : \text{every } G \text{ on } n \text{ vertices with } \delta(G) \ge d \text{ contains } C_4 \,\}, \qquad \exists N\; \forall n \ge N,\; f(n+1) \ge f(n)
$$

Here $\delta(G)$ is the minimum degree and $C_4$ the $4$-cycle. It is known that $f(n) \sim \sqrt{n}$, but whether $f$ is eventually monotone is OPEN. The formalization goal is to faithfully state the monotonicity question in Lean 4, prove the routine facts about the threshold function and the $C_4$-containment predicate, and isolate the deep asymptotic results and the open monotonicity core as clearly-labelled assumptions.

### Plain Language

For each number of vertices $n$, there is a smallest minimum-degree value $f(n)$ that forces any graph to contain a $4$-cycle. It is known that $f(n)$ grows roughly like the square root of $n$, but a natural-looking question remains unsolved: does $f$ eventually stop dipping — is $f(n+1) \ge f(n)$ for all large $n$? This project completes and hardens the existing Lean formalization of Erdős Problem #85: we do not settle the monotonicity question, but we make the statement precise, prove the routine supporting facts, and mark the deep asymptotic results and the open core as explicit assumptions.

### Why This Matters

1. **Subtle Monotonicity Gap**: Even though $f(n) \sim \sqrt{n}$ is well understood, whether the threshold is genuinely monotone is unexpectedly unresolved.
2. **Extremal–Ramsey Bridge**: The threshold $f(n)$ connects Kővári–Sós–Turán extremal bounds on $C_4$-free graphs to the Ramsey number $R(C_4, K_{1,n})$.
3. **Honest Formalization**: A faithful Lean statement, isolating the asymptotics and the open monotonicity core as named assumptions, keeps the gallery entry credible and gives a machine-checkable target.

## Known Results

### What's Already Proven

- The asymptotic $f(n) \sim \sqrt{n}$ is established, driven by the Kővári–Sós–Turán bound on the maximum size of $C_4$-free graphs — stated in the gallery Lean file as an axiom.
- The connection between $f(n)$ and the Ramsey number $R(C_4, K_{1,n})$ is captured in the source.
- Basic Lean definitions (the $4$-cycle graph $C_4$, the `containsC4` embedding predicate, the threshold `minDegreeForC4`, and the eventual-monotonicity `Erdos85Question`) already type-check with 0 sorries.

### What's Still Open

- Whether $f(n+1) \ge f(n)$ for all large $n$ — the main monotonicity question.
- Whether $f$ is only "almost monotone," decreasing by at most a bounded constant.
- The exact relationship between $f(n)$ and $R(C_4, K_{1,n})$, and a characterization of extremal $C_4$-free graphs with high minimum degree.

### Our Goal

Strengthen `Proofs/Erdos85Problem.lean` toward a maximally-honest state by (1) proving from Mathlib the routine facts about `SimpleGraph.minDegree` and the `containsC4` predicate (well-definedness, basic monotonicity in the degree parameter of the threshold set), (2) verifying that `containsC4` correctly encodes a genuine $4$-cycle embedding, and (3) reducing the axiom surface to the $f(n) \sim \sqrt{n}$ asymptotics and the open monotonicity statement, documenting each assumption precisely in `meta.json`. We must NOT claim to resolve the monotonicity question.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-85 | Parent gallery entry being completed | SimpleGraph.minDegree, C4-containment predicate, Filter.Tendsto asymptotics |
| erdos-64 | Sibling extremal-graph-theory entry on minimum degree forcing a cycle | SimpleGraph structure, minimum-degree cycle-forcing, axiomatized deep results |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Discharge the threshold and predicate lemmas.
   - Why it might work: `minDegreeForC4` as a `min` over a set of degree values, and the `containsC4` embedding predicate, admit basic well-definedness and monotonicity facts from Mathlib's `SimpleGraph.minDegree` and `Finset` APIs.
   - Risk: the threshold is defined via a minimum over graphs of size $n$; proving it is well-defined (the set is nonempty and bounded) requires care.

2. **Approach B**: Bundle the asymptotics and open core into an `Erdos85Axioms` structure.
   - Why it might work: collecting the $\sqrt{n}$ asymptotics and the eventual-monotonicity statement as fields makes the assumption inventory explicit and keeps the main statement readable.
   - Risk: per the Axiom Integrity Policy, structure fields remain assumptions and must be counted in `axiomCount`; this reorganizes but does not reduce the debt.

### Key Difficulties

- The monotonicity question is open, so its core cannot be discharged; work is limited to faithful statement and routine scaffolding.
- Faithfully encoding `containsC4` as an actual $4$-cycle embedding (injective, adjacency-preserving) rather than a weaker walk condition is the central correctness subtlety.

### What Would a Proof Need?

- Key lemma 1: well-definedness of `minDegreeForC4` (nonemptiness and boundedness of the threshold set).
- Key lemma 2: a faithful `containsC4` predicate as an injective adjacency-preserving embedding of $C_4$.
- Technical requirements: correct use of `Filter.Tendsto`/`Filter.atTop` for the $\sqrt{n}$ asymptotics and honest axiom accounting for the open monotonicity core.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The open part is a single narrow monotonicity question, so most of the file is faithful statement and routine scaffolding that Mathlib can support.
- The $\sqrt{n}$ asymptotics come from Kővári–Sós–Turán and must remain axiomatized, but the threshold and $C_4$-embedding lemmas are within reach.
- Mathlib provides `SimpleGraph.minDegree`, `Filter.Tendsto`, and `Filter.atTop` for the mechanical parts.

**Estimated Effort**:
- Exploration: one to two days to map the encoding and axiom surface.
- If tractable: about one to two weeks to discharge scaffolding lemmas and verify the $C_4$ predicate.
- If hard: the monotonicity core remains open and axiomatized indefinitely.

## References

### Papers
- Kővári, Sós, Turán, "On a problem of K. Zarankiewicz," Colloquium Mathematicum, 1954 — the extremal bound on $C_4$-free graphs underlying $f(n) \sim \sqrt{n}$.
- Erdős, "Extremal problems in graph theory," 1964 — origin of the minimum-degree $4$-cycle threshold and monotonicity question.

### Online Resources
- https://erdosproblems.com/85 — canonical statement and open status of Erdős Problem #85.

### Mathlib
- Mathlib.Combinatorics.SimpleGraph.Basic — `SimpleGraph` adjacency structure for encoding graphs and $C_4$.
- Mathlib.Combinatorics.SimpleGraph.Degree — `SimpleGraph.minDegree` for the minimum-degree threshold.
- Mathlib.Order.Filter.AtTopBot — `Filter.atTop` and `Filter.Tendsto` for the $\sqrt{n}$ asymptotics.

## Metadata

```yaml
tags:
  - erdos
  - graph-theory
  - extremal
  - 4-cycle
  - minimum-degree
  - formalization
  - conjecture
related_proofs:
  - erdos-85
  - erdos-64
difficulty: medium
source: proof-suggestion
created: 2026-07-09T17:33:20-07:00
```

**Significance**: 7/10
**Tractability**: 6/10
