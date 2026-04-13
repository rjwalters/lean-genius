# Problem: Complete polya_cyclic_fixed_count Bijection

**Slug**: burnside-counting-oq-03-oq-01
**Created**: 2026-04-04T21:47:52-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{polya\_cyclic\_fixed\_count}: |\{\text{colorings } f : \mathbb{Z}/d\mathbb{Z} \to \text{Fin}\,k \mid \sigma \cdot f = f\}| = k^{\gcd(\text{ord}(\sigma), d)}
$$

The bijection $\{\text{fixed colorings}\} \leftrightarrow (\text{Fin}\,d \to \text{Fin}\,k)$ — specifically the `left_inv` direction — needs to be proved.

### Plain Language

In the Burnside/Pólya counting framework, a coloring of $d$ positions with $k$ colors is "fixed" by a cyclic permutation $\sigma$ if $\sigma$ maps each coloring to itself. The number of such fixed colorings equals $k^{\gcd(\text{ord}(\sigma), d)}$.

The Lean proof constructs a bijection between fixed colorings and functions on orbits, but the **backward direction** (`invFun` composed with the forward map = `id`) is sorry'd. Specifically: showing that coloring by orbit representative and then evaluating at a representative gives back the original coloring.

### Why This Matters

This lemma is the core combinatorial step in the Pólya Enumeration Theorem proof. Completing it closes a concrete gap in Lean's formalization of necklace counting — a classical result with applications to chemistry, music theory, and combinatorial enumeration.

## Known Results

### What's Already Proven

- Forward direction (`toFun`) of the bijection is defined
- `invFun` (backward map) is defined but `left_inv` is sorry'd
- `MulAction.fixedPoints` API is available in Mathlib
- Orbit structure of cyclic groups on `Fin d` is understood
- `burnside-counting-oq-03` proves the outer Burnside sum formula

### What's Still Open

- `left_inv`: if `f` is a fixed coloring, then `invFun (toFun f) = f`
- Requires: for each `i`, `f(orbit_rep(i)) = f(i)` (from `f` being fixed by `σ`)

### Our Goal

Prove the `left_inv` direction of the bijection in `polya_cyclic_fixed_count`. This is a concrete sorry in an existing Lean file.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| burnside-counting-oq-03 | Parent proof using this lemma | Burnside's lemma, MulAction |
| burnside-counting | Burnside's lemma formalization | MulAction.fixedPoints |

## Initial Thoughts

### Potential Approaches

1. **Direct orbit argument**: Since `f` is fixed by `σ`, all elements in the same orbit have the same color. So `f(orbit_rep(i)) = f(i)` follows by induction on the orbit.
   - Why it might work: Mathlib has orbit API (`MulAction.orbit`, `MulAction.orbitEquivQuotient`)
   - Risk: Need to establish orbit representative is in the same orbit as `i`

2. **Fixed point characterization**: Use `MulAction.mem_fixedPoints` to unfold "fixed by σ" directly.
   - Why it might work: Direct API match to the hypothesis
   - Risk: Definitional unfolding may be messy

### Key Difficulties

- Connecting abstract orbit representative with the concrete `σ^n(i)` orbit path
- Lean type checking on the bijection construction (universe levels, coercion)

### What Would a Proof Need?

- Key lemma: For fixed coloring `f`, `∀ i, f i = f (orbitRep i)` — from `f` being equivariant
- Technical: `Finset.orbit_eq` or equivalent, `MulAction.fixedPoints` unfolding

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Gap is isolated: one `left_inv` sorry in an otherwise complete bijection
- Mathlib has all necessary orbit/action APIs
- Mathematical argument is clear: fixed colorings are constant on orbits

**Estimated Effort**:
- Exploration: 1-2 hours (locate sorry, understand bijection setup)
- If tractable: 1-3 days (fill sorry with orbit induction)

## References

### Papers
- Pólya, G. (1937) "Kombinatorische Anzahlbestimmungen für Gruppen, Graphen und chemische Verbindungen"

### Mathlib
- `Mathlib.GroupTheory.GroupAction.Basic` — `MulAction.fixedPoints`, `MulAction.orbit`
- `Mathlib.GroupTheory.GroupAction.Quotient` — orbit quotient machinery
- `Mathlib.Data.Finset.Card` — cardinality of orbit intersections

## Metadata

```yaml
tags:
  - combinatorics
  - group-theory
  - counting
  - necklaces
  - polya-enumeration
  - burnside
related_proofs:
  - burnside-counting-oq-03
  - burnside-counting
difficulty: medium
source: gallery-gap
created: 2026-04-04T21:47:52-07:00
```
