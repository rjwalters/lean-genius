# Problem: Binary bracelet counts b(7)=18, b(8)=30 via the generic dihedral action — kernel-decide feasibility frontier

**Slug**: burnside-counting-oq-04-oq-01-oq-01-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Using the generic dihedral group action on binary necklaces from the parent, prove the unconditional bracelet counts
$$
b(7) = 18, \qquad b(8) = 30 \qquad (\text{OEIS A000029}),
$$
and identify the `n` at which the kernel-reduced `decide` of the Burnside fixed-point sum
$$
b(n) = \frac{1}{|D_n|}\sum_{g \in D_n} |\mathrm{Fix}(g)|
$$
stops being feasible, motivating a symbolic per-element fixed-point formula in its place.

### Plain Language

The parent established `b(5)=8` and `b(6)=13` (binary bracelets — two-color necklaces up to rotation **and** reflection) by a fully kernel-checked Burnside count over a generic dihedral action, with no `native_decide`. This leaf pushes the same machinery to `n = 7, 8` (the next OEIS A000029 values, 18 and 30) and charts the practical frontier: where does the kernel `decide` blow up in time/memory, and at what point must one replace the brute fixed-point enumeration with the closed Burnside/Möbius formula?

### Why This Matters

It turns an isolated pair of computed values into a *method-scaling study*: the value of the parent's "native-decide-free" approach is precisely that it is axiom-clean, but kernel reduction scales poorly. Documenting exactly where it breaks — and supplying the symbolic fixed-point count that does scale — converts a one-off computation into a reusable, axiom-light recipe for bracelet enumeration.

### Why This Matters (continued)

The closed form `b(n) = (1/2)·(necklace count) + (correction for reflections)` with `necklace(n) = (1/n)·Σ_{d|n} φ(d) 2^{n/d}` is the target symbolic replacement, kept 0-axiom by avoiding `native_decide`.

## Known Results

### What's Already Proven

- Parent `burnside-counting-oq-04-oq-01-oq-01`: `b(5)=8`, `b(6)=13` via a generic dihedral action, kernel `decide`, no `native_decide` (0-axiom).
- Mathlib: `DihedralGroup`, `Fintype.card`, Burnside / `MulAction` orbit-counting infrastructure, `Nat.totient`, `Nat.divisors`, `decide`.

### What's Still Open

- The unconditional values `b(7)=18`, `b(8)=30`.
- The empirical/structural point where kernel `decide` becomes infeasible.
- A symbolic per-element fixed-point formula that reproduces the values without `native_decide`.

### Our Goal

Prove `b(7)=18` and `b(8)=30` reusing the parent's generic dihedral action; if kernel `decide` is too slow at `n=8`, derive and use the symbolic fixed-point count (rotations: `Σ_{d|n} φ(d) 2^{n/d}`; reflections: `n` even/odd split) so the result stays 0-axiom.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `burnside-counting-oq-04-oq-01-oq-01` | parent: b(5), b(6) via generic dihedral action | Burnside, `DihedralGroup`, kernel `decide` |
| `burnside-counting` | base Burnside / orbit-counting lemma | group actions, fixed points |

## Initial Thoughts

### Potential Approaches

1. **Extend kernel `decide` directly**: instantiate the parent's fixed-point sum at `n = 7` then `n = 8` and let kernel reduction close it.
   - Why it might work: `n=7` (`|D_7| = 14`, `2^7 = 128`) is likely still within kernel-reduction reach.
   - Risk: `n=8` (`2^8 = 256`, reflections split by parity) may exceed practical kernel-reduction limits — this is exactly the frontier to document.

2. **Symbolic fixed-point formula**: prove the per-element fixed-point counts symbolically (rotation by `k` fixes `2^{gcd(k,n)}` strings; reflections fix `2^{⌈n/2⌉}` or `2^{n/2}+2^{n/2}`-type counts by parity) and sum, giving `b(n)` for all `n` without enumeration.
   - Why it might work: each fixed-point count is a clean `gcd`/parity expression; the sum is a finite `Nat.divisors`/`Finset` computation.
   - Risk: matching Mathlib's `DihedralGroup` element indexing to the rotation/reflection fixed-point counts.

### Key Difficulties

- Keeping everything kernel-checkable (no `native_decide`) while the search space grows.
- Reflection fixed-point counts depend on the parity of `n` (axis through vertices vs edges).

### What Would a Proof Need?

- Key lemma 1: rotation `r^k` fixes `2^{gcd(k,n)}` binary strings.
- Key lemma 2: reflection fixed-point count by parity of `n`.
- Key lemma 3: Burnside division yields integer `b(n)`, evaluated to 18 and 30.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- `n=7` is a direct, near-mechanical extension of the parent.
- The symbolic formula is classical and the components exist in Mathlib (`Nat.gcd`, `Nat.totient`).
- Charting the `decide` frontier is empirical but concrete (build timing/memory).

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–3 days (n=7, n=8 + frontier note, possibly symbolic formula)
- If hard: a fully general 0-axiom `b(n)` closed form

## References

### Papers
- N. J. A. Sloane, OEIS A000029 (bracelets / two-color necklaces up to rotation and reflection).

### Online Resources
- OEIS A000029: 1, 2, 3, 4, 6, 8, 13, 18, 30, 46, …

### Mathlib
- `Mathlib/GroupTheory/SpecificGroups/Dihedral.lean` — `DihedralGroup`.
- `Mathlib/GroupTheory/GroupAction/...` and Burnside infrastructure; `Mathlib/NumberTheory/Divisors.lean` for `Σ_{d|n} φ(d) 2^{n/d}`.

## Metadata

```yaml
tags:
  - combinatorics
  - group-action
  - burnside
  - dihedral-group
  - bracelets
  - orbit-counting
related_proofs:
  - burnside-counting-oq-04-oq-01-oq-01
  - burnside-counting
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
