# Problem: Steiner (20) and Kirkman (60) Point Counts for the Hexagrammum Mysticum

**Slug**: pascals-hexagon-oq-03-wip-01
**Created**: 2026-07-09
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For a non-degenerate conic $C$ and six points on it (an inscribed hexagon),
the 60 Pascal lines of the Hexagrammum Mysticum meet in structured
configurations. Two counting theorems remain as `sorry` in
`PascalsHexagonOQ03.lean`:

$$
\#\{\text{Steiner points}\} = 20, \qquad \#\{\text{Kirkman points}\} = 60.
$$

Concretely, complete the two Lean theorems:

```lean
theorem steiner_count_eq_20 (C : Conic) (hex : InscribedHexagon C)
    [Fintype (SteinerPoint C hex)] :
    Fintype.card (SteinerPoint C hex) = 20

theorem kirkman_count_eq_60 (C : Conic) (hex : InscribedHexagon C)
    [Fintype (KirkmanPoint C hex)] :
    Fintype.card (KirkmanPoint C hex) = 60
```

### Plain Language

Pascal's theorem says the three pairs of opposite sides of a hexagon inscribed
in a conic meet in three collinear points, on the *Pascal line*. The six
vertices can be relabeled in $6!/(2\cdot 6) = 60$ essentially distinct ways,
giving 60 Pascal lines. These 60 lines are not in general position: triples of
them concur at special points. **Steiner points** (20 of them) are where three
Pascal lines meet in one family of triples; **Kirkman points** (60 of them)
arise from a complementary family. This problem asks for a machine-checked
proof of the counts 20 and 60.

### Why This Matters

The Hexagrammum Mysticum is a classical (Steiner 1828, Kirkman 1849,
Cayley/Salmon) but combinatorially intricate configuration whose modern
description uses the outer automorphism of $S_6$ (Conway–Ryba 2012).
Formalizing the point counts turns the S1 scaffold in the gallery into a
verified statement and exercises Lean's `Fintype.card` machinery on a
non-trivial projective-combinatorial object.

## Known Results

### What's Already Proven

- `pascals-hexagon-oq-03` (gallery, S1 scaffold) — defines `Conic`, `InscribedHexagon`, `HexagonLabeling`, `pascalLine`, `SteinerPoint`, `KirkmanPoint` and proves the surrounding structure; only the two count theorems are `sorry`.
- Pascal's theorem itself (parent `pascals-hexagon` entry) — concurrency/collinearity of the three intersection points.
- Conway–Ryba (2012) — the $S_6$-outer-automorphism description giving the 20 Steiner triples.

### What's Still Open

- `steiner_count_eq_20`: the cardinality of `SteinerPoint C hex` is 20.
- `kirkman_count_eq_60`: the cardinality of `KirkmanPoint C hex` is 60.

### Our Goal

Discharge both `sorry`s. The likely route is to establish a bijection between
`SteinerPoint`/`KirkmanPoint` and an explicit finite index set (the 20 Steiner
triples / 60 Kirkman triples of labelings), then compute the cardinality by
`Fintype.card` of that index set, avoiding the full projective-geometry
incidence computation.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| pascals-hexagon-oq-03 | The file containing the two `sorry`s | `Fintype.card`, projective incidence, `Finset` |
| pascals-hexagon | Base Pascal's theorem (concurrency of Pascal line) | conics, cross-ratio, projective geometry |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Explicit combinatorial index set**: Define the 20 Steiner
   triples (resp. 60 Kirkman triples) as an explicit `Finset` of triples of
   `HexagonLabeling`, prove `SteinerPoint C hex ≃ {this Finset}`, then
   `Fintype.card_congr` reduces to `decide`/`Finset.card` on the concrete set.
   - Why it might work: sidesteps hard projective incidence; the counts become finite combinatorics.
   - Risk: constructing the bijection still needs the concurrency facts (that each listed triple genuinely concurs and that distinct triples give distinct points).

2. **Approach B — $S_6$ outer-automorphism action**: Encode the Conway–Ryba
   labeling of Steiner/Kirkman points via the outer automorphism and count
   orbits.
   - Why it might work: matches the cleanest modern proof.
   - Risk: formalizing the outer automorphism of $S_6$ in Lean is itself substantial.

### Key Difficulties

- Establishing injectivity: distinct Steiner (resp. Kirkman) triples yield distinct concurrency points — needs genericity of the six points on $C$.
- Ensuring the `Fintype` instances in the theorem hypotheses agree with the constructed enumeration.

### What Would a Proof Need?

- Key lemma 1: an explicit enumeration of the 20 Steiner triples / 60 Kirkman triples of labelings, with a proof that each triple's three Pascal lines concur.
- Key lemma 2: distinctness of the resulting points (injectivity of triple → point).
- Technical requirements: `Fintype.card_congr`, `Equiv`, `Finset` combinatorics, and the incidence lemmas from the parent file.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The mathematics is classical and fully understood, but the formalization couples projective incidence with $S_6$ combinatorics.
- The scaffold already provides the definitions, narrowing the task to two cardinality proofs.
- Injectivity (distinctness of points) under genericity is the main technical obstacle.

**Estimated Effort**:
- Exploration: 3-5 days
- If tractable: 2-3 weeks
- If hard: 1-2 months

## References

### Papers
- J. Conway & A. Ryba, "The Pascal Mysticum Demystified", *Math. Intelligencer* 34 (2012) — the modern $S_6$ account with the 20/60 counts.
- G. Salmon, *A Treatise on Conic Sections* — classical enumeration of Steiner and Kirkman points.

### Online Resources
- https://en.wikipedia.org/wiki/Pascal%27s_theorem#Hexagrammum_Mysticum — configuration overview.

### Mathlib
- `Mathlib.LinearAlgebra.Projectivization` — projective points and lines.
- `Mathlib.Data.Fintype.Card` — `Fintype.card`, `Fintype.card_congr` for the counting step.

## Metadata

```yaml
tags:
  - projective-geometry
  - combinatorics
  - hexagrammum-mysticum
related_proofs:
  - pascals-hexagon-oq-03
  - pascals-hexagon
difficulty: high
source: gallery-gap
created: 2026-07-09
```
