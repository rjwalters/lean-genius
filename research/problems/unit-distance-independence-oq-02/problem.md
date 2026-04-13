# Problem: Hadwiger-Nelson Upper Bound via Hexagonal 7-Coloring

**Slug**: unit-distance-independence-oq-02
**Created**: 2026-04-05T19:30:03-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\chi(\mathbb{R}^2) \leq 7
$$

Specifically: prove `hadwiger_nelson_upper_bound ≤ 7` in Lean by formalizing the
hexagonal 7-coloring construction — a periodic tiling of the plane with regular
hexagons where vertices at unit distance always receive different colors.

### Plain Language

The chromatic number of the plane χ(ℝ²) is the minimum number of colors needed to
color every point of the plane so that no two points at distance exactly 1 share a
color. The hexagonal argument shows 7 colors suffice: tile the plane with regular
hexagons of diameter slightly less than 1, then color them using 7 colors in a periodic
pattern such that no two hexagons of the same color are within unit distance.

### Why This Matters

This is one half of the Hadwiger-Nelson problem: 4 ≤ χ(ℝ²) ≤ 7. The exact value
(now known to be ≥ 5 via de Grey's 2018 construction) remains open. The upper bound
proof is elementary but requires careful geometric argument about hexagon sizes and
distances. Formalizing it in Lean would:
1. Complete the known bounds for the Hadwiger-Nelson problem in the gallery
2. Establish geometric coloring infrastructure for further work
3. Demonstrate periodic tiling arguments in Lean 4

## Known Results

### What's Already Proven

- `unit-distance-independence`: `hadwiger_nelson_lower_bound ≥ 4` via Moser spindle
  (4-chromatic unit-distance graph, VERIFIED in gallery)
- de Grey (2018): χ(ℝ²) ≥ 5 (1581-vertex construction, not yet in gallery)
- The upper bound 7 is classical (Nelson, 1950)

### What's Still Open

- Exact value of χ(ℝ²): known to be 5, 6, or 7
- `hadwiger_nelson_lower_bound ≥ 5` (de Grey, needs separate formalization)
- Fractional chromatic number χ_f(ℝ²) ≥ 3.5 (Frankl-Wilson 1981)

### Our Goal

Prove `hadwiger_nelson_upper_bound ≤ 7` by constructing an explicit 7-coloring
of ℝ² where unit-distance points have different colors. This is the upper bound
direction, complementing the existing lower bound in the gallery.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `unit-distance-independence` | Direct parent — establishes lower bound ≥ 4 | Graph coloring, Moser spindle |
| `four-color-theorem` | Coloring infrastructure | Graph chromatic theory |
| `feuerbachs-theorem-defs` | Geometric distance computations | Euclidean geometry |

## Initial Thoughts

### Potential Approaches

1. **Hexagonal tiling construction**: Tile the plane with regular hexagons of diameter
   `d` where `1/√3 < d < 1`. Use a 7-periodic coloring. Prove that any two same-colored
   hexagons have distance > 1.
   - Why it might work: Standard constructive proof, well-known
   - Risk: Distance calculations in Lean 4 might require careful `norm_num` or `native_decide`
   - Key lemma: Minimum distance between same-colored hexagons in the periodic 7-coloring

2. **Discrete finite check**: Exhibit an explicit finite subgraph of the plane graph
   that 7-colors properly, then extend by periodicity.
   - Why it might work: Reduces to a finite combinatorial check
   - Risk: Periodicity argument requires more infrastructure

3. **Mathlib hexagonal lattice**: If Mathlib has hexagonal lattice definitions, leverage them.

### Key Difficulties

- Defining the hexagonal tiling formally (hexagon vertices, containment)
- Proving the periodicity of the coloring function
- Establishing the distance lower bound between same-colored hexagons

### What Would a Proof Need?

- Key lemma 1: Regular hexagon with diameter d < 1 has all internal distances < 1
- Key lemma 2: In the 7-periodic hexagonal coloring, adjacent hexagons (touching) have different colors
- Key lemma 3: Non-adjacent same-colored hexagons are at distance > 1
- Technical: Euclidean distance computations, `ℝ²` or `EuclideanSpace ℝ (Fin 2)`

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematical argument is elementary and classical (Nelson 1950)
- Distance calculations in Lean 4 can be verbose but are well-supported
- `EuclideanSpace ℝ (Fin 2)` is available in Mathlib
- `Finset.sup` and coloring definitions exist
- Main challenge: Formalizing the "hexagon contains the point" predicate

**Estimated Effort**:
- Exploration: 1-2 hours (understand Mathlib geometry API)
- If tractable: 2-3 days for full proof
- Key blocker: Mathlib hexagonal lattice support (may need to build from scratch)

## References

### Papers
- Nelson (1950) — Original 7-coloring argument (unpublished, cited in Hadwiger 1945)
- Hadwiger (1945) — "Überdeckung des euklidischen Raumes durch kongruente Mengen"
- de Grey (2018) — "The chromatic number of the plane is at least 5" (arXiv:1804.02385)

### Mathlib
- `Mathlib.Analysis.InnerProductSpace.Basic` — Euclidean geometry
- `Mathlib.Combinatorics.Graph.Coloring` — Graph coloring definitions
- `EuclideanSpace ℝ (Fin 2)` — The plane as Lean type

## Metadata

```yaml
tags:
  - graph-theory
  - chromatic-number
  - geometry
  - euclidean-plane
  - coloring
related_proofs:
  - unit-distance-independence
  - four-color-theorem
difficulty: medium
source: gallery-gap
created: 2026-04-05T19:30:03-07:00
```
