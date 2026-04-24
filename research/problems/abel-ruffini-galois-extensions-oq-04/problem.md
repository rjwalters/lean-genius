# Problem: Jordan-Hölder Uniqueness Theorem: Composition Factors of Finite Groups in Lean

**Slug**: abel-ruffini-galois-extensions-oq-04
**Created**: 2026-04-24
**Status**: Active
**Source**: proof-suggestion
**Parent Proof**: abel-ruffini-galois-extensions

## Problem Statement

### Formal Statement

State and prove the **Jordan-Hölder uniqueness theorem** in Lean 4:

> For any finite group $G$, every composition series of $G$ has the same length, and the multiset of composition factors (simple quotients $G_i/G_{i+1}$) is unique up to permutation and isomorphism.

As a concrete instantiation: the chain $\{e\} \trianglelefteq V_4 \trianglelefteq A_4 \trianglelefteq S_4$ is (up to isomorphism) the unique composition series of $S_4$, with factors $\mathbb{Z}/2, \mathbb{Z}/2, \mathbb{Z}/3, \mathbb{Z}/2$.

### Plain Language

Every finite group can be "broken down" into simple groups in a unique way — you can refine a composition series in any order, but you always end up with the same set of simple building blocks. This is the fundamental uniqueness theorem for group structure, analogous to the uniqueness of prime factorization.

### Why This Matters

- The Jordan-Hölder theorem is foundational to the classification of finite simple groups (CFSG)
- It makes the solvability criterion concrete: $S_4$ is solvable iff its composition factors are all abelian (they are: $\mathbb{Z}/2, \mathbb{Z}/2, \mathbb{Z}/3, \mathbb{Z}/2$)
- The parent proof `abel-ruffini-galois-extensions` uses composition series but relies on Mathlib's `CompositionSeries` API as a black box — this entry would expose the uniqueness theorem explicitly

## Mathlib Infrastructure

Relevant Mathlib modules:
- `Mathlib.GroupTheory.CompositionSeries` — `CompositionSeries`, `JordanHolderModule`
- `Mathlib.GroupTheory.Subgroup.Basic` — normal subgroups
- `Mathlib.GroupTheory.SolvableGroup` — solvable groups, derived series
- `Mathlib.GroupTheory.Sylow` — Sylow theorems (for S₄ analysis)
- `Mathlib.GroupTheory.SpecificGroups.Alternating` — A₄ properties

Key Mathlib lemma to locate: `CompositionSeries.jordan_holder` or similar uniqueness result.

## Research Goals

1. Locate or prove `jordan_holder_uniqueness` in Lean 4 / Mathlib
2. Instantiate for $S_4$: name and type-check the composition series $\{e\} \trianglelefteq V_4 \trianglelefteq A_4 \trianglelefteq S_4$
3. State the theorem: factors of $S_4$ are $\{(\mathbb{Z}/2)^3, \mathbb{Z}/3\}$
4. Verify this implies solvability (all factors abelian)

## Approach Candidates

### Approach 1: Mathlib Direct (Recommended)
Check if `Mathlib.GroupTheory.CompositionSeries` already has the uniqueness theorem. If so, provide a clean formalization that:
- States the theorem explicitly as a named `theorem`
- Instantiates it for $S_4$
- Connects to `abel-ruffini-galois-extensions` solvability argument

### Approach 2: Custom Proof
If Mathlib's theorem is implicit, prove uniqueness directly using:
- Induction on composition series length
- Zassenhaus butterfly lemma
- Schreier refinement theorem

## Related Gallery Proofs

- `abel-ruffini-galois-extensions`: parent proof, uses composition series for $S_4$ solvability
- `abel-ruffini-oq-04`: exposes $A_5$ simplicity → derived series → Abel-Ruffini chain
- `abel-ruffini-oq-04-oq-02`: proves $S_2, S_3, S_4$ solvable via explicit derived series
- `sylow-theorem`: Sylow theorems (active claim) — useful for factor analysis
