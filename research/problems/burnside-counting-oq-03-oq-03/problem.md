# Problem: Interface Burnside's Lemma with Mathlib MulAction Framework

**Slug**: burnside-counting-oq-03-oq-03
**Created**: 2026-04-05
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The gallery proof `BurnsideCounting.lean` uses `AddAction (ZMod n)` for cyclic rotation
of colorings, but Mathlib's orbit-counting theorem operates on `MulAction`. The goal is
to build a proper `MulAction (ZMod n).toMultiplicativeGroup (Coloring n k)` instance
(or equivalent bridge) so that all 5 current axioms collapse to `native_decide` or
Mathlib lemmas:

1. `rotatedIndex_add` — modular arithmetic composition law for rotations
2. `fixed_point_sum_binary_4` — computed fixed-point sum = 24
3. `coloringSetoid` — orbit equivalence relation
4. `coloringQuotientFintype` — Fintype instance for quotient
5. `binary_necklaces_4` — 6 distinct binary 4-necklaces

### Plain Language

The current Burnside's lemma formalization axiomatizes 5 facts that "should" be decidable
or follow from Mathlib's group theory library. The missing bridge is a group homomorphism
from (ℤ/nℤ, +) to (Sym(Coloring n k), ∘) that expresses cyclic rotation as a `MulAction`.
Once this bridge exists, `coloringSetoid` and `coloringQuotientFintype` can be derived from
Mathlib's `orbitRel`, `rotatedIndex_add` becomes a `decide`-able modular identity, and
`fixed_point_sum_binary_4` reduces to `native_decide`.

### Why This Matters

Removing these 5 axioms would change the gallery proof from `badge: "axiom"` to potentially
`badge: "verified"`. It also provides a reusable pattern for any future necklace/orbit
counting problem in Lean 4 that uses cyclic group actions.

## Known Results

### What's Already Proven

- `burnside_lemma` — wraps `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`
- `binary_4_colorings_count` — `Coloring 4 2` has 16 elements (fully proved)
- `constant_coloring_count` — exactly k constant colorings (fully proved)
- `period2_count` — 4 binary colorings of length 4 with period dividing 2 (fully proved)
- `rotateColoring` — ZMod n acts on colorings by cyclic rotation (definition)
- `cyclicAddActionOnColorings` — `AddAction (ZMod n) (Coloring n k)` instance

### What's Still Open

- Bridge `AddAction (ZMod n)` → `MulAction` for orbit-counting API
- Formal proof that cyclic rotation forms a valid group action (rotatedIndex_add)
- Decision procedure for the fixed-point sum (fixed_point_sum_binary_4)
- Quotient structure for the orbit equivalence (coloringSetoid, coloringQuotientFintype)

### Our Goal

Eliminate all 5 axioms by:
1. Proving `rotatedIndex_add` via modular arithmetic lemmas in Mathlib
2. Using `native_decide` or `decide` for `fixed_point_sum_binary_4` and `binary_necklaces_4`
3. Building a `MulAction` instance from the `AddAction` and deriving `coloringSetoid`/`coloringQuotientFintype` from `orbitRel`

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| burnside-counting | Parent proof — the axioms to eliminate | Group actions, ZMod, necklaces |
| burnside-counting-oq-03 | Sibling OQ extending to Pólya enumeration | Pólya cycle index |

## Initial Thoughts

### Potential Approaches

1. **ZMod-to-MulAction bridge via `MonoidHom`**:
   - Define `φ : ZMod n →+ Equiv.Perm (Coloring n k)` sending rotation `r` to the permutation `c ↦ rotateColoring r c`
   - Use `AddMonoidHom.toMulAction` or similar to extract a `MulAction`
   - Risk: Lean 4's `AddAction` and `MulAction` are not directly interchangeable; need careful instance derivation

2. **Direct `rotatedIndex_add` proof**:
   - `rotatedIndex i r := (i + n - r) % n`
   - Show `rotatedIndex (rotatedIndex i r₁) r₂ = rotatedIndex i (r₁ + r₂)` (mod n)
   - This is elementally provable by `omega` or `ZMod` arithmetic lemmas
   - Risk: Low — standard modular arithmetic

3. **`native_decide` for finite computations**:
   - `fixed_point_sum_binary_4` is a finite sum over 4 group elements, each fixed-point count decidable
   - `binary_necklaces_4` is a finite cardinality claim
   - Both should yield to `native_decide` once the action is properly defined

### Key Difficulties

- Bridging `AddAction (ZMod n)` to `MulAction` requires finding the right Mathlib API path
- `coloringSetoid` and `coloringQuotientFintype` depend on proper orbit equivalence; needs `orbitRel` from Mathlib
- Lean 4 definitional equality issues may arise with `ZMod` modular reduction

### What Would a Proof Need?

- Key lemma 1: `rotatedIndex_add` via `Nat.add_mod`, `Nat.sub_mod`, or `omega`
- Key lemma 2: `MonoidHom` from `(ZMod n).toMultiplicativeGroup` to `Equiv.Perm (Coloring n k)`
- Key lemma 3: Derivation of `orbitRel (ZMod n) (Coloring n k)` from Mathlib's `MulAction.orbitRel`
- Technical: `Fintype` instance for `Quotient (orbitRel (ZMod n) (Coloring n k))`

## Tractability Assessment

**Difficulty**: Low-Medium

**Justification**:
- `rotatedIndex_add` is pure modular arithmetic — provable with `omega` or existing `Nat.mod` lemmas
- `native_decide` handles the finite computation axioms
- The MulAction bridge is the main challenge, but Mathlib has `ZMod` group structures and `Equiv.Perm` MulAction instances

**Estimated Effort**:
- Exploration: 1-2 days (finding the right Mathlib API)
- If tractable: 2-4 days to eliminate all 5 axioms

## References

### Mathlib
- `Mathlib.GroupTheory.GroupAction.Basic` — `MulAction`, `orbitRel`, `sum_card_fixedBy_eq_card_orbits_mul_card_group`
- `Mathlib.Data.ZMod.Basic` — `ZMod` as `CommRing`, `AddCommGroup`
- `Mathlib.GroupTheory.Perm.Basic` — `Equiv.Perm` as `MulAction` on the base type
- `Mathlib.Algebra.Group.Hom.Basic` — `MonoidHom`, `AddMonoidHom.toMulAction`

## Metadata

```yaml
tags:
  - combinatorics
  - algebra
  - group-theory
  - mathlib-integration
  - necklace-counting
  - burnside
  - connection
related_proofs:
  - burnside-counting
  - burnside-counting-oq-03
difficulty: low-medium
source: gallery-gap
created: 2026-04-05
```
