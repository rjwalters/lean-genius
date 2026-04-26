# Problem: Minkowski Fundamental Theorem — Custom Lattice API vs ZLattice Comparison

**Slug**: minkowski-fundamental-theorem-oq-04
**Created**: 2026-04-22
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The existing formalization uses a custom `Lattice n` type bridged to Mathlib's `ZSpan`.
Mathlib provides `ZLattice` in `Mathlib.Algebra.Module.ZLattice.Basic`. The question is
whether and how these APIs relate, and whether refactoring to `ZLattice` would simplify
or improve the formalization.

### Plain Language

The Minkowski Fundamental Theorem proof in this gallery uses a bespoke `Lattice n` structure
(basis matrix + invertibility) with a bridging construction (`Lattice.toModuleBasis`) to
connect to Mathlib's geometry-of-numbers API. Mathlib independently defines `ZLattice` as
a canonical lattice type. This problem investigates the relationship between these two APIs:
their expressive power, the effort to bridge between them, and which is better suited for
downstream number theory formalizations.

### Why This Matters

- **Mathlib alignment**: A `ZLattice`-native proof would be directly reusable by the Mathlib
  community without requiring users to understand the custom Lattice wrapper.
- **Downstream proofs**: Minkowski's second theorem, class number bounds for algebraic number
  fields, and Blichfeldt's generalization all build on the same lattice infrastructure.
- **API design lesson**: Documents the concrete tradeoffs between user-friendly custom types
  and Mathlib canonical structures — a recurring design tension in Lean formalization.

## Known Results

### What's Already Proven

- `minkowski_fundamental` — proved using custom Lattice API + ZSpan bridge
- `MinkowskiProved.minkowski_integer_lattice_proved` — direct proof for ℤⁿ using Mathlib types
- `MinkowskiProved.minkowski_general_lattice_proved` — proof via Module.Basis
- `fermat_from_minkowski` — Fermat's two squares theorem derived from the formalization

The current proof (662 lines, 0 sorries, 0 axioms) is complete and verified.

### What's Still Open

- How `ZLattice` compares to the custom `Lattice n` in API coverage and ergonomics
- Whether `Lattice.toModuleBasis` can be replaced by existing `ZLattice` infrastructure
- Whether a `ZLattice`-native proof would be shorter or longer

### Our Goal

Produce a structured comparison of the custom API vs `ZLattice`, and if feasible, a
`ZLattice`-native version of the key bridging constructions.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `minkowski-fundamental-theorem` | Parent proof — the custom API being compared | Custom Lattice, ZSpan bridge, Module.Basis |

## Initial Thoughts

### Potential Approaches

1. **API comparison document**: Read `MinkowskiFundamentalTheorem.lean` and the Mathlib
   `ZLattice` source side by side. Document what each provides and where they overlap.
   - Why it might work: The proof is complete, so we're doing analysis not synthesis.
   - Risk: Low. This is tractable documentation/comparison work.

2. **Refactoring attempt**: Try replacing `Lattice n` with `ZLattice` in a new file.
   - Why it might work: `ZLattice` should have `basis`, `covolume`, and span machinery.
   - Risk: Medium. `ZLattice` may lack some API coverage, requiring new lemmas.

### Key Difficulties

- `ZLattice` in Mathlib is defined differently (as a subtype, not as basis matrix data)
- The custom API stores basis as `Matrix (Fin n) (Fin n) ℝ` with explicit covolume
- Bridging may require understanding `AddSubgroup` ↔ `Module.Basis` correspondences

### What Would a Proof Need?

- Survey of `ZLattice` API: what theorems exist in `Mathlib.Algebra.Module.ZLattice.*`?
- Identify: does Mathlib have `ZLattice.covolume` or `ZLattice.fundamentalDomain`?
- Check: `ZSpan.isAddFundamentalDomain` — is this the same as what `ZLattice` uses?

## Tractability Assessment

**Difficulty**: Low-Medium (comparison) / Medium (refactoring)

**Justification**:
- The source proof is already complete and well-annotated
- The question is architectural, not about proving new mathematics
- `ZLattice` machinery exists in Mathlib and just needs to be surveyed

**Estimated Effort**:
- Exploration (OBSERVE + ORIENT): 1-2 sessions
- Comparison document: 1 session
- Refactoring attempt (if warranted): 2-4 sessions

## References

### Mathlib

- `Mathlib.Algebra.Module.ZLattice.Basic` — ZLattice definition and basic API
- `Mathlib.Algebra.Module.ZLattice.Covolume` — covolume theory (if it exists)
- `Mathlib.Analysis.InnerProductSpace.PiL2` — EuclideanSpace machinery
- `proofs/Proofs/MinkowskiFundamentalTheorem.lean` — the custom API to compare against

## Metadata

```yaml
tags:
  - number-theory
  - lattices
  - mathlib
  - geometry-of-numbers
  - api-comparison
  - zlattice
  - refactoring
related_proofs:
  - minkowski-fundamental-theorem
difficulty: low-medium
source: gallery-gap
created: 2026-04-22
```

**Significance**: 7/10
**Tractability**: 7/10
