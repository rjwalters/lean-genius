# Problem: Complete the Erdős #70 Partition-Calculus Formalization

**Slug**: erdos-70-wip-01
**Created**: 2026-07-09T17:33:19-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\text{Erdős70}:\quad \forall\, \beta < \omega_1,\ \forall\, n\ (2 \le n < \omega),\qquad \mathfrak{c} \to (\beta, n)^3_2, \qquad \mathfrak{c} = 2^{\aleph_0}.
$$

### Plain Language

The gallery entry `erdos-70` formalizes Erdős Problem #70 in partition calculus — whether the continuum $\mathfrak{c}$ satisfies the arrow relation $\mathfrak{c} \to (\beta, n)^3_2$ for every countable ordinal $\beta$ — but it carries a `wip` badge: two deep external theorems (Erdős–Rado's $\mathfrak{c} \to (\omega+n,4)^3_2$ and the finite Ramsey theorem) are stated as assumptions, and the order-type condition is approximated by a cardinality proxy. This research problem is to strengthen the formalization: prove the definitional and monotonicity lemmas fully, replace the cardinality proxy with a faithful order-type condition where feasible, and cleanly isolate the genuinely open core, moving toward `verified` without claiming to settle the open problem.

### Why This Matters

1. **Faithful arrow semantics**: The partition arrow $\kappa \to (\alpha, m)^n_k$ is only meaningful if the order-type parameter is encoded correctly; upgrading the cardinality proxy toward true order type makes the Lean statement match the mathematics.
2. **Reusable set-theoretic scaffolding**: Colorings of $n$-subsets, homogeneous sets, and ordinal-arithmetic countability lemmas over Mathlib's `Cardinal`/`Ordinal` API are reusable across Ramsey-theoretic entries.
3. **Sharp open boundary**: The first genuinely open case is $\mathfrak{c} \to (\omega^2, n)^3_2$; making the known/open split explicit in Lean pinpoints exactly where the Erdős–Rado stepping-up stops.

## Known Results

### What's Already Proven

- Erdős–Rado (1956): $\mathfrak{c} \to (\omega+n, 4)^3_2$ for all $2 \le n < \omega$, via the stepping-up lemma — *Bull. AMS* 62 (1956). Currently an assumption in the Lean file.
- Finite Ramsey theorem: $\forall r,k,n,\ \exists N,\ N \to (r)^n_k$ — assumed in the file; the specific 3-subset-of-a-3-set case is proved from definitions.
- Monotonicity of the arrow (in both the ordinal and the size parameter), and countability of $\omega+n$ and $\omega^2$, are proved from Mathlib's `Ordinal`/`Cardinal` API in `Proofs/Erdos70Problem.lean`.

### What's Still Open

- Whether $\mathfrak{c} \to (\omega^2, n)^3_2$ holds — the first case beyond Erdős–Rado, open in mathematics.
- Whether $\mathfrak{c} \to (\omega^\omega, n)^3_2$ holds, and whether the answer is independent of ZFC.

### Our Goal

Advance `erdos-70` from `wip` toward `verified` by: (1) proving the remaining definitional lemmas about `Coloring`, `IsHomogeneous`, and `nSubsets` directly; (2) replacing the `HasOrderTypeAtLeast` cardinality proxy with a faithful order-type condition (or documenting precisely why the proxy is used and where it weakens the statement); (3) confirming the only remaining assumptions are the two genuine external theorems (Erdős–Rado, finite Ramsey) and the open conjecture, and updating meta.json `axiomCount`/`status` to match. No claim to resolve the open problem.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-70 | Parent entry being completed; same arrow, colorings, and ordinal lemmas | `Cardinal`, `Ordinal`, `Finset`, partition arrow, stepping-up |
| ramseys-theorem | Finite predecessor of the partition arrow; grounds the homogeneous-set definitions | monochromatic subsets, pigeonhole, Ramsey numbers |

## Initial Thoughts

### Potential Approaches

1. **Approach A — harden the definitional layer**: fully prove properties of `Coloring`, `IsHomogeneous`, and `nSubsets` (e.g. a 3-set is trivially homogeneous for its 3-subsets), leaving only Erdős–Rado, finite Ramsey, and the open conjecture as assumptions.
   - Why it might work: these are finite/definitional facts within reach of Mathlib's `Finset` API.
   - Risk: the `Set` vs `Finset` variants of homogeneity may need bridging lemmas that are tedious.

2. **Approach B — upgrade the order-type proxy**: replace `HasOrderTypeAtLeast` (a cardinality bound) with a genuine `Ordinal.typein`/order-embedding condition.
   - Why it might work: Mathlib has `Ordinal` order-type machinery for well-orders.
   - Risk: extracting an order embedding from a homogeneous subset of an unordered `Set` may require choosing a well-order, complicating the statement.

### Key Difficulties

- The headline conjecture and the $\omega^2$ case are genuinely open; they can only be *stated*, so the win is faithfulness and clarity, not resolution.
- Erdős–Rado's stepping-up and full finite Ramsey are substantial theorems far beyond current Mathlib, so they remain explicit assumptions.

### What Would a Proof Need?

- Key lemma 1: consistency of the `Set` and `Finset` homogeneity definitions, and basic closure properties of `nSubsets`.
- Key lemma 2: a faithful order-type comparison replacing the cardinality proxy, or a precise statement of the proxy's limitation.
- Technical requirements: careful use of `Cardinal.continuum`, `Ordinal.card`, and `Ordinal.card_le_card`, plus a meta.json audit of the two remaining assumptions.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The definitional and monotonicity lemmas are tractable, but faithfully encoding order type (not just cardinality) in Mathlib's `Ordinal` API is genuinely delicate.
- Similar set-theory entries have kept deep theorems (Erdős–Rado) axiomatized while tightening the surrounding scaffolding; that partial path is realistic here.
- Mathlib's `Cardinal`/`Ordinal` modules cover countability and monotonicity, but order-embedding extraction from unordered homogeneous sets is at the edge of routine.

**Estimated Effort**:
- Exploration: 2–3 days to assess how far the order-type proxy can be upgraded.
- If tractable: 2–4 weeks to prove definitional lemmas and tighten the arrow semantics.
- If hard: the open cases and full Erdős–Rado remain out of scope.

## References

### Papers
- P. Erdős and R. Rado, "A partition calculus in set theory", *Bull. Amer. Math. Soc.* 62 (1956), 427–489 — foundational arrow notation and stepping-up.
- S. Todorčević, "Partitioning pairs of countable ordinals", *Acta Mathematica* 159 (1987), 261–294 — advances on countable-ordinal partitions.

### Online Resources
- https://erdosproblems.com/70 — canonical statement and status.

### Mathlib
- `Mathlib.SetTheory.Cardinal.Continuum` — `Cardinal.continuum` and $2^{\aleph_0}$.
- `Mathlib.SetTheory.Ordinal.Arithmetic` — ordinal arithmetic, `Ordinal.card`, and order-type machinery for the arrow.

## Metadata

```yaml
tags:
  - erdos
  - partition-calculus
  - set-theory
  - ramsey-theory
  - ordinals
  - formalization
related_proofs:
  - erdos-70
  - ramseys-theorem
difficulty: high
source: proof-suggestion
created: 2026-07-09T17:33:19-07:00
```

**Significance**: 8/10
**Tractability**: 5/10
