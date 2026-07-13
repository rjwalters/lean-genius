# Problem: Dual Schröder–Bernstein — Mutual Surjections Imply Equinumerosity

**Slug**: schroeder-bernstein-oq-05
**Created**: 2026-07-01
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: schroeder-bernstein

## Problem Statement

### Formal Statement

$$
(\exists\, f : A \twoheadrightarrow B)\ \wedge\ (\exists\, g : B \twoheadrightarrow A)
\ \Rightarrow\ \exists\, h : A \xrightarrow{\ \sim\ } B
$$

### Plain Language

If there exist surjections $f : A \to B$ and $g : B \to A$, then $A$ and $B$ are
equinumerous. This is the **dual** Schröder–Bernstein theorem. Unlike the injective form
(which holds in ZF), the surjective form genuinely requires the axiom of choice: each
surjection is turned into an injection the other way by choosing a section (right inverse),
after which the ordinary Schröder–Bernstein theorem applies. The entry pinpoints exactly
where choice enters (the two section choices).

### Why This Matters

This answers the parent's explicitly listed unanswered open question #4 (the surjective /
dual formulation). All existing siblings treat the injective input case: oq-01 (categorical
SBP), oq-02 (Knaster–Tarski fixed-point proofs), oq-03 (Myhill computable isomorphism),
oq-04 (constructive/decidability content). The dual is a distinct theorem with a distinct
foundational subtlety — its dependence on choice.

## Known Results

### What's Already Proven

- Parent entry `schroeder-bernstein` is verified (0-axiom).
- Mathlib supplies `Function.Embedding.schroeder_bernstein` (mutual injections ⇒ bijection),
  `Function.Surjective.hasRightInverse`, and `Function.RightInverse.injective`.

### What's Still Open

- The target theorem below (currently `sorry`), plus the Equiv/Cardinal corollary.

### Our Goal

Prove the sketch below as a verified child of `schroeder-bernstein` (note: the result is a
theorem *of ZFC* — its proof legitimately uses `Classical.choice`; the entry documents this
rather than claiming choice-freeness). Category: **extension**.

## Target Lean Sketch

```lean
open Function

theorem dual_schroeder_bernstein {α β : Type*} {f : α → β} {g : β → α}
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    ∃ h : α → β, Function.Bijective h := by
  obtain ⟨f', hf'⟩ := hf.hasRightInverse   -- f' : β → α, section of f, injective
  obtain ⟨g', hg'⟩ := hg.hasRightInverse   -- g' : α → β, section of g, injective
  exact Function.Embedding.schroeder_bernstein hg'.injective hf'.injective

-- corollary: bundled equinumerosity
theorem dual_schroeder_bernstein_equiv {α β : Type*} {f : α → β} {g : β → α}
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Nonempty (α ≃ β) := by sorry -- via Function.Embedding.antisymm on the two embeddings
```

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `schroeder-bernstein` | Parent: mutual injections ⇒ bijection | fixed-point / orbit analysis |
| `schroeder-bernstein-oq-02` | Sibling: Knaster–Tarski fixed-point proof | lattice fixed points |

## Tractability Assessment

**Difficulty**: Low

**Significance**: 6/10  |  **Tractability**: 8/10  |  **Tier**: B

**Justification**: The headline is a three-line composition of named Mathlib lemmas; the
mathematical content is the *framing* (dual statement, isolating the two `Classical.choice`
invocations that make the dual choice-dependent).

### Suggested First Steps

1. State for arbitrary `Type*` α, β with two surjections; obtain sections via
   `hf.hasRightInverse` / `hg.hasRightInverse`.
2. Convert each section to an injection with `.injective`, then feed into
   `Function.Embedding.schroeder_bernstein`.
3. Add the `Nonempty (α ≃ β)` corollary via `Function.Embedding.antisymm`, plus a docstring
   note isolating the two `Classical.choice` uses.

## References

### Mathlib

- `Function.Surjective.hasRightInverse` — Logic/Function/Basic.lean (the choice step)
- `Function.RightInverse.injective` — Logic/Function/Basic.lean
- `Function.Embedding.schroeder_bernstein` — SetTheory/Cardinal/SchroederBernstein.lean
- `Function.Embedding.antisymm` — SetTheory/Cardinal/SchroederBernstein.lean

## Metadata

```yaml
tags:
  - set-theory
  - cardinality
  - schroeder-bernstein
  - axiom-of-choice
  - surjections
related_proofs:
  - schroeder-bernstein
  - schroeder-bernstein-oq-02
difficulty: low
source: proof-suggestion
created: 2026-07-01
```
