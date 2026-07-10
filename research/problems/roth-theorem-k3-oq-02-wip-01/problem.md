# Problem: Triangle-Count Bounds in the Ruzsa-Szemeredi Graph for Roth via Triangle Removal

**Slug**: roth-theorem-k3-oq-02-wip-01
**Created**: 2026-07-09
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Complete the two `sorry`s in `RothTriangleRemoval.lean` that bound the triangle
count of the Ruzsa–Szemerédi graph $G_A$ built from an AP-free set
$A \subseteq \mathbb{Z}/N\mathbb{Z}$ ($N$ odd):

```lean
-- (1) Upper bound on ordered triangle triples when A is AP-free
lemma rs_tc_ap_free_le (A : Finset (ZMod N)) (hAP : APFree A) (hOdd : Odd N) :
    triangleCount (ruzsaSzemerediGraph A) univ univ univ ≤ 6 * A.card * N

-- (2) Removal lower bound: any triangle-destroying edge set is large
lemma rs_removal_lb (A : Finset (ZMod N)) (hAP : APFree A) (hOdd : Odd N)
    (R : Finset (RSVertex N × RSVertex N))
    (hR : /- R removes every triangle -/) :
    A.card * N ≤ R.card
```

Together with the triangle removal lemma these give Roth's theorem: an AP-free
subset of $\{1,\dots,N\}$ has density $o(1)$.

### Plain Language

Roth's theorem states that any subset of the integers with positive density
contains a 3-term arithmetic progression. One elegant proof encodes an AP-free
set $A$ as a tripartite graph $G_A$ whose triangles correspond exactly to
3-APs. Because $A$ is AP-free, every triangle of $G_A$ is "degenerate" (comes
from a trivial progression $a,a,a$), so there are few triangles — yet each edge
sits in a triangle, so removing all triangles needs many edges. The Triangle
Removal Lemma then forces $A$ to be sparse. This problem fills the two
counting lemmas that make that argument rigorous in Lean.

### Why This Matters

The graph-theoretic proof of Roth's theorem (Ruzsa–Szemerédi) is a landmark
connecting additive combinatorics and extremal graph theory, and it is the
gateway to Szemerédi's theorem and the Green–Tao theorem. The surrounding
scaffolding (`ruzsaSzemerediGraph`, `triangleCount`, `APFree`, the removal
lemma interface) is already in place in the gallery; closing these two
lemmas completes a fully verified Roth proof via triangle removal.

## Known Results

### What's Already Proven

- `roth-theorem-k3-oq-02` (gallery, `RothTriangleRemoval.lean`) — defines `ruzsaSzemerediGraph`, `RSVertex`, `triangleCount`, `APFree`, `removeEdges`; proves `ap_free_forces_equal` (in an AP-free set every triangle is $\{(0,x),(1,x+a),(2,x+2a)\}$) and the vertex-count lemma; only the two counting bounds are `sorry`.
- The Triangle Removal Lemma interface (consumed downstream to finish Roth).
- Mathlib's `SimpleGraph`, `triangleFinset`/`cliqueFinset`, and `Finset.card` API.

### What's Still Open

- `rs_tc_ap_free_le`: at most $6\,|A|\,N$ ordered triangle triples when $A$ is AP-free (each of the $|A|\cdot N$ unordered triangles counted $\le 6$ ways).
- `rs_removal_lb`: any edge set $R$ that destroys every triangle satisfies $|R| \ge |A|\,N$ (each XY-edge lies in exactly one triangle, so distinct edges are needed per triangle).

### Our Goal

Discharge both `sorry`s. For (1), use `ap_free_forces_equal` to show the
unordered triangles are exactly indexed by $(a,x) \in A \times \mathbb{Z}/N$,
then multiply by the $\le 6$ orderings. For (2), show each of the $|A|\,N$
XY-edges lies in a *unique* triangle, so a triangle-free-making $R$ must
contain a distinct edge per triangle.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| roth-theorem-k3-oq-02 | The file containing the two `sorry`s | Ruzsa–Szemerédi graph, `triangleCount`, `APFree` |
| szemeredi-regularity | Regularity/removal-lemma infrastructure Roth builds on | Szemerédi regularity, counting lemma |
| szemeredi-theorem | Downstream generalization (k-APs) | density increment, regularity |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Bijective triangle enumeration (for lemma 1)**: Build an
   explicit injection from unordered triangles of `ruzsaSzemerediGraph A` into
   $A \times \mathbb{Z}/N$ using `ap_free_forces_equal`, giving $|A|\,N$
   unordered triangles; bound `triangleCount` (ordered) by $6\times$ that with
   a permutation-counting lemma.
   - Why it might work: `ap_free_forces_equal` already pins the triangle shape.
   - Risk: relating Lean's `triangleCount` (ordered triples over `univ³`) to the unordered enumeration needs a clean $\le 6$ overcount bound.

2. **Approach B — Unique-triangle-per-edge (for lemma 2)**: Prove each XY-edge
   is in exactly one triangle, define the map (triangle ↦ its XY-edge), show it
   is injective into $R$, conclude $|A|\,N \le |R|$ by `Finset.card_le_card`.
   - Why it might work: uniqueness follows from AP-freeness plus the graph's tripartite structure.
   - Risk: formalizing "removeEdges makes it triangle-free ⇒ R hits each triangle" requires care with the `hR` hypothesis quantifiers.

### Key Difficulties

- Bridging `triangleCount` (ordered, over three `univ` vertex sets) and the natural unordered $(a,x)$-indexed enumeration.
- Proving each XY-edge belongs to exactly one triangle (uniqueness), which underpins the removal lower bound.

### What Would a Proof Need?

- Key lemma 1: unordered triangles of $G_A$ $\simeq A \times \mathbb{Z}/N$ (via `ap_free_forces_equal`).
- Key lemma 2: each XY-edge lies in exactly one triangle of $G_A$.
- Key lemma 3: `triangleCount` (ordered) $\le 6 \cdot$ (number of unordered triangles).
- Technical requirements: `SimpleGraph.Adj`, `Finset.card_le_card`, injection-counting lemmas, `ZMod N` arithmetic with $N$ odd.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The proof sketches are already written in the file's comments; the mathematics is fully understood.
- `ap_free_forces_equal` does the hardest combinatorial work; the remaining steps are counting/injection arguments well supported by Mathlib's `Finset` API.
- Main friction is the ordered-vs-unordered triangle bookkeeping, not new mathematics.

**Estimated Effort**:
- Exploration: 1-2 days
- If tractable: 1-2 weeks
- If hard: 3-4 weeks (if `triangleCount` bridging proves fiddly)

## References

### Papers
- I. Z. Ruzsa & E. Szemerédi, "Triple systems with no six points carrying three triangles" (1978) — origin of the removal-lemma proof of Roth.
- K. F. Roth, "On certain sets of integers" (1953) — the theorem itself.

### Online Resources
- https://en.wikipedia.org/wiki/Ruzsa%E2%80%93Szemer%C3%A9di_problem — the graph and its connection to Roth.

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.Triangle.Basic` — triangle counting and the removal lemma.
- `Mathlib.Data.ZMod.Basic` — `ZMod N` arithmetic used for the vertex labels.

## Metadata

```yaml
tags:
  - additive-combinatorics
  - graph-theory
  - roth-theorem
related_proofs:
  - roth-theorem-k3-oq-02
  - szemeredi-regularity
  - szemeredi-theorem
difficulty: medium
source: gallery-gap
created: 2026-07-09
```
