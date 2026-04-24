# Problem: Jordan-Hölder Uniqueness Theorem: Composition Factors of Finite Groups in Lean

**Slug**: abel-ruffini-galois-extensions-oq-04
**Created**: 2026-04-24T00:00:00Z
**Status**: Active
**Source**: gallery-gap <!-- OQ4 from abel-ruffini-galois-extensions -->

## Problem Statement

### Formal Statement

$$
\text{For any finite group } G, \text{ every composition series}
\\ G = G_0 \trianglerighteq G_1 \trianglerighteq \cdots \trianglerighteq G_n = \{e\}
\\ \text{has the same length, and the multiset of composition factors}
\\ \{G_i / G_{i+1}\}_{i=0}^{n-1}
\\ \text{is unique up to isomorphism and reordering.}
$$

### Plain Language

A **composition series** of a finite group $G$ is a maximal chain of normal subgroups:
$$\{e\} = G_n \trianglelefteq G_{n-1} \trianglelefteq \cdots \trianglelefteq G_0 = G$$
where each factor $G_i/G_{i+1}$ is **simple** (no proper non-trivial normal subgroups).

The Jordan-Hölder theorem asserts: no matter how you build such a chain, you always get the same simple groups (up to order and isomorphism). The theorem implies composition length is well-defined and that composition factors are group-theoretic invariants.

### Why This Matters

- Provides the group-theoretic foundation for the Abel-Ruffini theorem: the composition factors of $S_n$ determine solvability by radicals
- Makes the chain $\{e\} \trianglelefteq V_4 \trianglelefteq A_4 \trianglelefteq S_4$ a **certified** witness, not just one example — any other composition series gives the same factors
- Connects to the classification of finite simple groups (CFSG): Jordan-Hölder gives meaning to CFSG as a complete catalog
- Fundamental to module theory (Krull-Schmidt) and representation theory

## Known Results

### What's Already Proven in the Gallery

- `abel-ruffini`: Abel-Ruffini theorem (degree ≥ 5 polynomials unsolvable by radicals)
- `abel-ruffini-galois-extensions`: Galois theory extension results (Galois correspondence, etc.)
- `abel-ruffini-oq-04`: A₅ simplicity and solvability chain $\{e\} \trianglelefteq V_4 \trianglelefteq A_4 \trianglelefteq S_4$

### Mathlib Status

Mathlib4 has `CompositionSeries` and the Jordan-Hölder theorem:
- `Mathlib.GroupTheory.CompositionSeries` — `CompositionSeries` type, `JordanHolderModule` class
- `CompositionSeries.jordan_holder` or similar — the uniqueness statement
- `IsoInvariant` — the equivalence relation on composition series

### What's Still Open

- Connecting Mathlib's abstract `JordanHolderModule` to concrete finite group instances
- Formalizing the explicit composition series for $S_4$ and verifying uniqueness
- Linking back to the Abel-Ruffini gallery proof's specific composition chains

### Our Goal

State and prove `jordan_holder_unique` for finite groups in Lean 4, connected to the existing `abel-ruffini-galois-extensions` gallery entry. The primary deliverable:
1. Formalize the Jordan-Hölder theorem using Mathlib's `CompositionSeries`
2. Instantiate for $S_4$: verify the $\{e\} \trianglelefteq V_4 \trianglelefteq A_4 \trianglelefteq S_4$ series is the unique (up to reordering) composition series
3. Connect to solvability: derive that $S_4$ is solvable from this chain

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `abel-ruffini-galois-extensions` | Parent proof — OQ4 source | Galois theory, normal subgroups |
| `abel-ruffini-oq-04` | $A_5$ simplicity, $S_4$ chain | Sylow theory, quotient groups |
| `abel-ruffini` | Main Abel-Ruffini theorem | Solvable groups, radicals |

## Initial Thoughts

### Potential Approaches

1. **Mathlib Direct** (High confidence): Use `Mathlib.GroupTheory.CompositionSeries` directly.
   - `CompositionSeries` is defined; `JordanHolderModule` provides the uniqueness infrastructure
   - Instantiate the typeclass for `Subgroup G` with `G` finite
   - Prove uniqueness as a corollary of `CompositionSeries.jordan_holder`
   - Risk: typeclass instance requirements may need work

2. **Concrete S₄ Instance**: Prove the specific $S_4$ composition series claim without full generality.
   - More tractable if Mathlib abstractions are hard to instantiate
   - Direct computation-style proof using `decide` or `Finset` enumeration
   - Risk: less theoretically interesting, won't generalize

3. **Via Lattice Theory**: Jordan-Hölder via modular lattices (Schreier refinement).
   - More abstract, stronger result
   - Risk: significant infrastructure needed

### Key Difficulties

- `JordanHolderModule` typeclass may need `IsSimple` and `Normal` instances for concrete groups
- Connecting abstract `CompositionSeries` to the specific chain in $S_4$
- Schreier refinement lemma may or may not be in Mathlib

### What Would a Proof Need?

- `CompositionSeries (Subgroup S4)` instance
- The specific series: `⊥ ≤ V4 ≤ A4 ≤ ⊤` as a `CompositionSeries`
- `CompositionSeries.jordan_holder` (or equiv.) applied to two distinct series
- Isomorphism witnesses for the composition factors

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Mathlib has substantial infrastructure for this (`CompositionSeries`, `JordanHolderModule`)
- The main work is instantiation and connecting to the gallery's specific group chain
- Not a moonshot — this is classical group theory with established Lean/Mathlib support
- Similar to how `abel-ruffini-oq-04` used existing Mathlib group theory

**Estimated Effort**:
- Exploration: 1-2 hours (search Mathlib, understand `CompositionSeries` API)
- If Mathlib direct works: 1-3 days
- If concrete instance only: 0.5-1 day

## References

### Mathlib
- `Mathlib.GroupTheory.CompositionSeries` — core infrastructure
- `Mathlib.GroupTheory.SolvableGroup` — solvability definitions
- `Mathlib.GroupTheory.Sylow` — Sylow theory (used in $S_4$ analysis)
- `Mathlib.GroupTheory.SpecificGroups.Alternating` — $A_n$ theorems

### Papers / Texts
- Lang, *Algebra* §I.4 — Jordan-Hölder theorem proof
- Dummit & Foote §3.3 — composition series and Jordan-Hölder

## Metadata

```yaml
tags:
  - algebra
  - group-theory
  - composition-series
  - jordan-holder
  - mathlib
related_proofs:
  - abel-ruffini-galois-extensions
  - abel-ruffini-oq-04
  - abel-ruffini
difficulty: medium
source: gallery-gap
created: 2026-04-24
```
