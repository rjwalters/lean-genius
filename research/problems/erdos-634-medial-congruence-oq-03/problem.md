# Problem: Which counts N admit a tiling of a triangle by N congruent copies of a triangle?

**Slug**: erdos-634-medial-congruence-oq-03
**Created**: 2026-07-09T17:03:07-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\text{Characterize } \mathcal{N} = \{\, N \in \mathbb{N} : \exists\, \text{triangles } T, R \text{ with } T \text{ tiled by } N \text{ non-overlapping congruent copies of } R \,\}.
$$

In particular, determine whether $\mathcal{N} = \mathbb{N}$, or find the precise set of forbidden counts, going beyond the perfect-square values
$$
N = k^2 \quad (k \ge 1)
$$
that the square (medial) reptiling always supplies.

### Plain Language

If you cut a triangle into $N$ smaller triangular pieces that are all congruent to one another (same shape and size, allowing reflections and rotations), which values of $N$ are possible? Reptiling — repeatedly applying the medial subdivision — shows that every perfect square $N = k^2$ works for *any* triangle. Erdős #634 asks for the full set of achievable $N$: which non-square counts are realizable, and are there any counts that no triangle can ever be split into?

### Why This Matters

This is Erdős Problem #634, a clean and still largely open question in combinatorial/discrete geometry. The parent gallery entry `erdos-634-medial-congruence` formalizes the base case $k=2$ of the square reptiling (four congruent half-scale copies) unconditionally over an arbitrary real normed space. The present problem asks for the *global* characterization of achievable counts $N$, which sits at the intersection of dissection theory, isometry groups, and number-theoretic constraints on how areas and side lengths must combine. A characterization would resolve a named Erdős problem and connect elementary tiling constructions to deeper structural obstructions.

## Known Results

### What's Already Proven

- **Square reptiling ($N = k^2$).** Every triangle tiles into $k^2$ congruent copies of a $1/k$-scale similar triangle, for all $k \ge 1$. The $k=2$ (medial) case is fully machine-checked in the parent proof `erdos-634-medial-congruence` — joining side midpoints yields four pairwise-congruent triangles with explicit isometry witnesses. Iterating gives all perfect squares.
- **$N = 1$ and small trivial counts.** $N=1$ is trivial; combining constructions (e.g. splitting a triangle into two congruent right triangles via an altitude of an isosceles triangle) shows further small counts are achievable for *specific* triangles.
- **$N = 3$ for special triangles.** A 30-60-90 triangle (and more generally certain right triangles) dissects into 3 congruent similar copies; likewise every triangle can be cut into $n$ congruent triangles for various $n$ by slicing parallel strips of a right triangle, giving all $n$ of a particular parity/shape family.
- **General strip/ladder constructions.** By subdividing one side into $m$ equal parts and drawing cevians, a right triangle can be cut into $m$ congruent triangles for every $m$; combined with reptiling this shows the achievable set is large.

### What's Still Open

- The **exact set $\mathcal{N}$** of counts $N$ achievable over *all* triangles $T$ (with $R$ allowed to depend on $T$) is not fully characterized — this is the core of Erdős #634.
- Whether **every** $N \ge 1$ is achievable (i.e. $\mathcal{N} = \mathbb{N}$), or whether some counts (candidates historically discussed include small values like $N=2,3,5$ for a *fixed* generic triangle) are forbidden.
- The refined question: for a **fixed** triangle $T$, which $N$ admit a tiling by congruent copies of some $R$ — and how does this set depend on the shape of $T$.

### Our Goal

We aim to formalize and extend the constructive side: (1) reprove/organize the reptiling family $N=k^2$ (already done for $k=2$), (2) formalize the strip construction giving $N=m$ congruent pieces of a right triangle, and (3) state the general characterization conjecture precisely as a Lean proposition so that partial results (achievable-set lower bounds, and any impossibility for a specific $(T,N)$) can be added incrementally.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-634-medial-congruence | Parent proof: formalizes the $k=2$ square-reptiling base case (four congruent medial triangles) with explicit isometry witnesses | Isometry-congruence of ordered triangles, `IsometryEquiv.constVAdd`, point reflection, midpoint API |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Constructive achievable-set lower bound.**
   Formalize two generating families: (i) reptiling $N \mapsto k^2 N$ (composing tilings) and (ii) the right-triangle strip construction giving $N = m$ for every $m$. Show closure under composition to establish a large explicit subset of $\mathcal{N}$.
   - Why it might work: both constructions are elementary and the medial base case is already formalized; the strip construction only needs equal-subdivision cevians and side-length bookkeeping.
   - Risk: bookkeeping of non-overlap and exact congruence in Lean is heavy; congruence requires exhibiting isometries as in the parent proof.

2. **Approach B — Impossibility via area/shape invariants.**
   For a *fixed* generic triangle $T$, attempt to rule out specific small $N$ using invariants: total area forces each piece to have area $\mathrm{area}(T)/N$, and congruence forces all pieces to be similar with ratio $1/\sqrt{N}$; combine with angle-sum and boundary-matching constraints to derive contradictions for forbidden $N$.
   - Why it might work: mirrors classic dissection impossibility arguments.
   - Risk: genuinely open in general; likely only yields conditional/partial impossibility, not a full characterization.

### Key Difficulties

- Deciding whether $\mathcal{N} = \mathbb{N}$ is essentially the open heart of Erdős #634; a complete answer may be out of reach.
- Encoding "non-overlapping tiling of a triangle" and "congruent copies" faithfully in Lean, and proving non-overlap, is substantial infrastructure beyond the pointwise congruence handled in the parent proof.
- Reflections vs. orientation-preserving isometries: whether $R$ may be used flipped changes some counts and must be fixed in the formal statement.

### What Would a Proof Need?

- Key lemma 1: a Lean definition of `TilesByCongruent T R N` (a finite family of congruent images of $R$ with pairwise-disjoint interiors covering $T$).
- Key lemma 2: composition/reptiling closure — if $T$ tiles into $a$ copies and each into $b$ copies, then $T$ tiles into $ab$ copies (gives $k^2$ and products).
- Key lemma 3: the strip construction — a right triangle tiles into $m$ congruent triangles for every $m \ge 1$.
- Technical requirements: area and side-length invariants, isometry witnesses (as in the parent proof), and interior-disjointness of the pieces.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The full characterization is a named, still-open Erdős problem; a complete Lean-verified answer is a moonshot for the impossibility direction.
- However, the **constructive lower-bound** portion (reptiling $k^2$ + strip $N=m$ + closure under products) is genuinely tractable and builds directly on the already-verified parent proof.
- Mathlib provides the isometry and midpoint machinery used by the parent proof; convex-geometry and measure tools exist for area but the tiling/non-overlap infrastructure would be new.

**Estimated Effort**:
- Exploration: 2-4 days
- If tractable (constructive subset + precise conjecture statement): 2-3 weeks
- If hard (impossibility / full characterization): unknown / open

## References

### Papers
- P. Erdős, list of problems — Problem #634 (dissections of a triangle into congruent triangles). See the Erdős Problems catalogue.
- W. T. Tutte and others, on dissecting shapes into congruent/similar pieces — background on rep-tiles.
- S. L. Snover, C. Waiveris, J. K. Williams, "Rep-tiling for triangles," *Discrete Mathematics* (1991) — which $N$ admit a triangle dissection into $N$ congruent similar triangles.

### Online Resources
- https://www.erdosproblems.com/634 — statement and status of Erdős Problem #634.
- https://en.wikipedia.org/wiki/Rep-tile — background on rep-tiles and reptiling of triangles.

### Mathlib
- `Mathlib.Topology.MetricSpace.IsometricSMul` — `IsometryEquiv.constVAdd`, translation isometries (used in the parent proof for congruence witnesses).
- `Mathlib.Analysis.Normed.Operator.LinearIsometry` — `LinearIsometryEquiv.neg`, negation as a linear isometry (point reflections).
- `Mathlib.LinearAlgebra.AffineSpace.Midpoint` — midpoint API for the medial construction.
- `Mathlib.Analysis.Convex.Combination` / `Mathlib.Analysis.Convex.Basic` — convex hulls of triangle vertices, for defining triangular pieces.

## Metadata

```yaml
tags:
  - geometry
  - erdos
  - dissection
  - congruence
  - isometry
  - reptile
related_proofs:
  - erdos-634-medial-congruence
difficulty: high
source: gallery-gap
created: 2026-07-09T17:03:07-07:00
```
