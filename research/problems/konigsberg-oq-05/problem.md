# Problem: Endpoints of an Eulerian Trail Are Exactly the Odd-Degree Vertices

**Slug**: konigsberg-oq-05
**Created**: 2026-07-01
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: konigsberg

## Problem Statement

### Formal Statement

For an Eulerian trail $p$ from $u$ to $v$ in a finite simple graph $G$:
$$
u = v \Rightarrow \forall x,\ \text{Even}(\deg x); \qquad
u \neq v \Rightarrow \big(\text{Odd}(\deg x) \iff x \in \{u,v\}\big).
$$
Hence any finite graph with $\ge 3$ odd-degree vertices admits no Eulerian trail with any
endpoints.

### Plain Language

Euler's theorem (used in the Königsberg parent) says an Eulerian trail forces the number
of odd-degree vertices to be 0 or 2, but not *which* vertices those are. This child
sharpens the necessity direction: a closed trail ($u=v$) forces every degree even, and an
open trail ($u \neq v$) makes the odd-degree set **exactly** the two endpoints $\{u,v\}$.
Combined with the handshaking lemma this yields a strengthened Königsberg impossibility:
$\ge 3$ odd-degree vertices $\Rightarrow$ no Eulerian trail at all.

### Why This Matters

Siblings cover concrete families / odd-regular graphs (oq-01), directed graphs (oq-02),
hypergraphs/infinite graphs (oq-03), and Eulerian-circuit counting/BEST (oq-04). None
establishes the *exact identity* of the odd-degree set with the trail's endpoints, nor the
"$\ge 3$ odd $\Rightarrow$ no trail" strengthening. This is a pure necessity-direction
result, so it verifies with 0 axioms (unlike siblings that axiomatize Hierholzer
sufficiency).

## Known Results

### What's Already Proven

- Parent `konigsberg` is verified.
- Mathlib has `SimpleGraph.Walk.IsEulerian.even_degree_iff`,
  `IsEulerian.card_filter_odd_degree`, and the handshaking lemma
  `SimpleGraph.even_card_odd_degree_vertices`.

### What's Still Open

- The target theorems below (currently `sorry`).

### Our Goal

Prove the sketch below as a verified (0-axiom) child. Category: **specialization
(necessity direction)**.

## Target Lean Sketch

```lean
open SimpleGraph SimpleGraph.Walk
variable {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] [DecidableEq V]

/-- Open-trail endpoints have odd degree. -/
theorem euler_open_endpoint_odd {u v : V} {p : G.Walk u v}
    (h : p.IsEulerian) (hn : u ≠ v) : Odd (G.degree u) ∧ Odd (G.degree v) := by
  sorry -- from IsEulerian.even_degree_iff at u and v; Nat.not_even_iff_odd

/-- The odd-degree set of an OPEN trail is exactly {u, v}. -/
theorem euler_open_odd_set {u v : V} {p : G.Walk u v}
    (h : p.IsEulerian) (hn : u ≠ v) :
    ∀ x, Odd (G.degree x) ↔ (x = u ∨ x = v) := by
  sorry -- negate even_degree_iff; ¬(x ≠ u ∧ x ≠ v) ↔ x = u ∨ x = v

/-- A CLOSED trail forces every degree even. -/
theorem euler_circuit_all_even {u : V} {p : G.Walk u u}
    (h : p.IsEulerian) : ∀ x, Even (G.degree x) := by
  sorry -- even_degree_iff with u = v makes RHS vacuously true

/-- Strengthened Königsberg: ≥ 3 odd vertices ⇒ no Eulerian trail. -/
theorem no_euler_trail_of_three_odd
    (h3 : 3 ≤ (Finset.univ.filter (fun x => Odd (G.degree x))).card) :
    ∀ (u v : V) (p : G.Walk u v), ¬ p.IsEulerian := by
  sorry -- IsEulerian.card_filter_odd_degree gives ∈ {0,2}; omega
```

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `konigsberg` | Parent: Seven Bridges / Euler trails | degree parity |
| `konigsberg-oq-04` | Sibling: Eulerian-circuit counting (BEST) | Eulerian circuits |
| `konigsberg-oq-01` | Sibling: concrete families / odd-regular | degree conditions |

## Tractability Assessment

**Difficulty**: Low

**Significance**: 6/10  |  **Tractability**: 8/10  |  **Tier**: B

**Justification**: Every theorem is a short (3-12 line) consequence of
`IsEulerian.even_degree_iff` plus `card_filter_odd_degree`. No new graph construction, no
Hierholzer sufficiency needed — pure necessity, fully 0-axiom.

### Suggested First Steps

1. Instantiate `IsEulerian.even_degree_iff` at `u` and `v` to get endpoint oddness.
2. Negate it to characterize the odd-degree set as `{u,v}` in the open case; use
   `even_degree_iff` with `u = v` for the closed case.
3. Use `IsEulerian.card_filter_odd_degree` (card ∈ {0,2}) and `omega` for the ≥3
   strengthening; optionally cross-check with `even_card_odd_degree_vertices`.

## References

### Mathlib

- `SimpleGraph.Walk.IsEulerian.even_degree_iff` — Combinatorics/SimpleGraph/Trails.lean
- `SimpleGraph.Walk.IsEulerian.card_filter_odd_degree`, `IsEulerian.card_odd_degree` — Combinatorics/SimpleGraph/Trails.lean
- `SimpleGraph.even_card_odd_degree_vertices`, `sum_degrees_eq_twice_card_edges` — Combinatorics/SimpleGraph/DegreeSum.lean
- `Nat.not_even_iff_odd`, `Finset.card_pair` — core

### Literature

- Euler (1736); standard graph-theory treatments of Eulerian trails.

## Metadata

```yaml
tags:
  - graph-theory
  - eulerian-trails
  - konigsberg
  - degree-parity
related_proofs:
  - konigsberg
  - konigsberg-oq-04
  - konigsberg-oq-01
difficulty: low
source: proof-suggestion
created: 2026-07-01
```
