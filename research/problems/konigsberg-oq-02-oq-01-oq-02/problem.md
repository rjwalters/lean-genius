# Problem: Undirected Eulerian Circuit Theorem (Euler's Characterization)

**Slug**: konigsberg-oq-02-oq-01-oq-02
**Created**: 2026-06-30T22:49:26-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $G = (V, E)$ be a finite, connected (multi)graph. Euler's theorem
characterizes when $G$ admits an *Eulerian circuit* — a closed walk that
traverses every edge exactly once — and an *Eulerian trail* — an open walk
with the same edge-covering property:

$$
G \text{ has an Eulerian circuit} \iff G \text{ is connected and } \deg(v) \text{ is even for every } v \in V.
$$

$$
G \text{ has an Eulerian trail} \iff G \text{ is connected and the number of odd-degree vertices is } 0 \text{ or } 2.
$$

Equivalently, writing $O = \{\, v \in V : \deg(v) \text{ is odd}\,\}$, a
connected graph has an Eulerian trail iff $|O| \in \{0, 2\}$; the circuit case
is exactly $|O| = 0$, and when $|O| = 2$ the trail must start at one odd-degree
vertex and end at the other. (The handshake lemma forces $|O|$ to be even, so
$|O| = 1$ is impossible.)

In the Mathlib formulation the target existence theorem reads:

$$
\bigl(G.\mathrm{Connected}\bigr) \;\wedge\; \bigl(\forall v,\ \mathrm{Even}\,(G.\deg v)\bigr)
\;\Longrightarrow\; \exists\, v_0\ (p : G.\mathrm{Walk}\ v_0\ v_0),\ p.\mathrm{IsEulerian} \wedge p.\mathrm{IsCircuit}.
$$

### Plain Language

This is the theorem that started graph theory. In 1736 Leonhard Euler was asked
whether one could stroll through Königsberg crossing each of its seven bridges
exactly once and return home. He proved it impossible, and in doing so isolated
the only thing that matters: the *parity of the degrees*. If you are going to
enter and leave every landmass without repeating a bridge, then every time you
arrive at a vertex you must also depart, so bridges get used up in pairs — every
vertex needs an even number of them. Königsberg had four landmasses all of odd
degree, so no such tour exists. Euler's insight is that this simple counting
obstruction is the *only* obstruction: a connected graph in which every vertex
has even degree can always be traced in one closed sweep.

### Why This Matters

This entry is the **undirected companion** to the parent gallery proof
`konigsberg-oq-02-oq-01`, which fully formalizes Hierholzer's algorithm for the
*directed* case (an Eulerian circuit exists iff the digraph is strongly
connected and every vertex is balanced, $\mathrm{indeg} = \mathrm{outdeg}$).
Completing the undirected characterization closes the classical Euler result in
its original form — the form that answers the Königsberg bridges question that
names this whole problem family. Together the directed and undirected theorems
give the complete Euler/Hierholzer picture, and the undirected trail corollary
($0$ or $2$ odd vertices) is what actually settles the historical puzzle.

## Known Results

### What's Already Proven

- **Directed Eulerian circuit theorem (parent).** `konigsberg-oq-02-oq-01`
  (`Proofs/KonigsbergOQ02OQ01.lean`, 0 sorries, 0 axioms) proves
  `directed_euler_circuit_sufficient_corrected`: a strongly connected, balanced
  finite digraph has an Eulerian circuit, via a full formalization of
  Hierholzer's algorithm — maximal-trail-is-a-circuit, `Walk.splice`,
  `removeArcList` residual-subgraph bookkeeping, and well-founded induction on
  arc count.
- **Necessary direction, undirected (Mathlib).** In
  `Mathlib/Combinatorics/SimpleGraph/Trails.lean`:
  - `SimpleGraph.Walk.IsEulerian` — the predicate that a trail covers every
    edge exactly once (`p.IsTrail ∧ ∀ e ∈ G.edgeSet, e ∈ p.edges`).
  - `SimpleGraph.Walk.IsEulerian.even_degree_iff` — for an Eulerian walk from
    $u$ to $v$, vertex $x$ has even degree iff $x \notin \{u,v\}$. This is the
    forward (necessity) half of the characterization.
  - `SimpleGraph.Walk.IsEulerian.card_odd_degree` — a graph with an Eulerian
    trail has $0$ or $2$ odd-degree vertices.
  - `SimpleGraph.Walk.IsTrail.even_countP_edges_iff`, `IsEulerian.isTrail`,
    `IsEulerian.edgeSet_eq`, `IsTrail.isEulerian_iff` — supporting lemmas.
- **Handshake lemma (Mathlib).** `SimpleGraph.even_card_odd_degree_vertices`
  (a.k.a. the sum-of-degrees / even-number-of-odd-vertices result) gives that
  $|O|$ is even for free.

### What's Still Open

- **The sufficiency (existence) direction is NOT in Mathlib.** Mathlib supplies
  only the "Eulerian $\Rightarrow$ even degrees" necessity lemmas. The
  constructive converse — "connected + even degrees $\Rightarrow$ an Eulerian
  circuit *exists*" — has no Mathlib proof and is the substance of this problem.
- The **multigraph modelling** question (parallel edges / loops) is unresolved:
  `SimpleGraph` cannot represent the actual seven-bridge Königsberg graph.

### Our Goal

Prove the sufficiency direction for `SimpleGraph`:

> For a finite, connected `SimpleGraph G` with `∀ v, Even (G.degree v)`, there
> exist `v₀` and a walk `p : G.Walk v₀ v₀` with `p.IsEulerian` (and hence
> `p.IsCircuit`).

Then derive the trail corollary ($0$ or $2$ odd vertices $\Rightarrow$ Eulerian
trail) by adding a virtual edge between the two odd vertices, reducing to the
even case, and deleting that edge. Combining this with Mathlib's necessity
lemmas yields the full iff.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| konigsberg-oq-02-oq-01 | Directed analogue; supplies the Hierholzer construction to port | maximal-trail-is-circuit, `Walk.splice`, `removeArcList`, WF induction on arc count |
| konigsberg-oq-02 | Grandparent; defines `Digraph`, `Walk`, `isEulerian`, degree theory | directed Euler framework |
| konigsberg | Original undirected Königsberg bridges impossibility (the historical root) | degree-parity obstruction |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Port Hierholzer from the directed parent via darts.** Model
   each undirected edge as a *matched pair of darts* (oriented half-edges), i.e.
   apply the parent's directed machinery to the symmetric digraph where every
   edge $\{a,b\}$ becomes both arcs $(a,b)$ and $(b,a)$. In that digraph
   $\mathrm{indeg}(v) = \mathrm{outdeg}(v) = \deg_G(v)$ automatically (balance is
   free), and connectivity of $G$ gives strong connectivity of the symmetrized
   digraph. The parent's `directed_euler_circuit_sufficient_corrected` then
   produces a directed circuit; the remaining work is to show it descends to an
   *undirected* Eulerian circuit that uses each undirected edge once rather than
   its two darts once each.
   - Why it might work: reuses a fully verified, 0-sorry Hierholzer engine; the
     dart correspondence is the standard textbook bridge between the cases.
   - Risk: the "use each edge once, not each dart once" descent is subtle — the
     directed circuit traverses $2|E|$ darts, and one must pair them so the
     undirected walk is a genuine trail. Interfacing the parent's bespoke
     `Digraph`/`Walk` types with Mathlib's `SimpleGraph.Walk` is glue work.

2. **Approach B — Native Hierholzer on `SimpleGraph.Walk`.** Reprove the
   algorithm directly for undirected walks: build a maximal trail from a
   positive-degree vertex, show even degree forces it to close into a circuit,
   splice in sub-circuits found in the edge-deleted residual graph, induct on
   `G.edgeFinset.card`.
   - Why it might work: stays entirely inside Mathlib's `SimpleGraph`,
     `Walk.IsTrail`, `Walk.IsCircuit`, `edgeSet`, `degree` API; the resulting
     theorem is stated in the idiomatic library types.
   - Risk: essentially redoing the parent's substantial proof, now with the
     added bookkeeping that deleting an *undirected* edge decrements *two*
     degrees, and with `Sym2 V` edge handling instead of ordered arcs.

3. **Approach C — Induction on the number of edges via cycle decomposition.**
   Prove the classical lemma that a graph with all-even degrees decomposes into
   edge-disjoint cycles, then stitch cycles together along shared vertices using
   connectivity.
   - Why it might work: the even-degree cycle-decomposition lemma is clean and
     independently useful.
   - Risk: "stitch along shared vertices" is again a splice argument; without
     care the stitching order needs connectivity in a form that is itself work
     to formalize.

### Key Difficulties

- **Multigraph modelling — the central wrinkle.** `SimpleGraph` forbids both
  parallel edges and loops, but the real Königsberg graph has *parallel* bridges
  between the same pair of landmasses. So the `SimpleGraph` theorem, while the
  right first target, does **not** literally decide the historical puzzle. To
  cover the genuine bridges instance one must model a multigraph: options are
  (a) Mathlib's `Quiver`/incidence style with an explicit edge type and an
  endpoint map $E \to \mathrm{Sym2}\,V$; (b) a `Multigraph` structure carrying
  edge multiplicities; or (c) simulate multiplicity by subdividing each parallel
  edge with a degree-2 dummy vertex (which preserves the parity of the original
  vertices and reduces the multigraph to a `SimpleGraph`). The subdivision trick
  (c) is the cheapest path to actually resolving Königsberg without new
  infrastructure, but it changes $E$ and must be argued to preserve Eulerian
  status.
- **Directed → undirected descent (if Approach A).** Turning a dart circuit into
  an edge trail requires a consistent pairing of the two darts of each edge and
  a proof that the resulting undirected walk is `IsTrail`.
- **Connectivity plumbing.** `SimpleGraph.Connected` / `Reachable` must be
  converted into the concrete "there is a vertex of the current circuit with an
  unused incident edge" statement that drives the splice step (the parent's
  `vertex_with_unused_arc` lemma is the directed template).
- **Even-degree residual bookkeeping.** Deleting a closed trail's edges must be
  shown to preserve the all-even-degree invariant on the residual graph (the
  undirected analogue of the parent's `removeArcList_balanced`).

### What Would a Proof Need?

- Key lemma 1: `maximal_trail_is_circuit` (undirected) — in an all-even-degree
  graph, a maximal trail (no unused edge at its final vertex) is closed.
- Key lemma 2: `Walk.splice` for `SimpleGraph.Walk` at a shared vertex, plus a
  trail-preservation lemma for edge-disjoint splices (port of the parent's
  `Walk.splice` / `splice_nodup`).
- Key lemma 3: even-degree preservation under deletion of a circuit's edge set
  (undirected `removeArcList_balanced`).
- Key lemma 4: connectivity $\Rightarrow$ some circuit vertex has an incident
  edge outside the circuit (undirected `vertex_with_unused_arc`).
- Technical requirement: well-founded recursion on `G.edgeFinset.card` (or the
  residual edge count), mirroring the parent's WF induction on `arcCount`.
- Corollary: the $0$-or-$2$-odd-vertex trail theorem via the virtual-edge
  reduction, and the multigraph statement via one of the modelling options.

## Tractability Assessment

**Difficulty**: Medium–High

**Justification**:
- The mathematics is completely classical and the *directed* version is already
  fully formalized in the gallery (0 sorries, 0 axioms) — this is adaptation,
  not invention. That is the strongest tractability signal.
- Mathlib already supplies half the iff (`IsEulerian.even_degree_iff`,
  `card_odd_degree`) and a rich `SimpleGraph.Walk`/`IsTrail`/`IsCircuit` API, so
  the necessity direction and much scaffolding are free.
- The remaining work is real: either porting the parent's ~950-line Hierholzer
  proof to undirected walks (Approach B) or building the dart correspondence and
  descent (Approach A). Neither is a one-liner.
- The multigraph modelling is the genuine wrinkle: the clean `SimpleGraph`
  theorem does not literally cover Königsberg's parallel bridges, so a faithful
  statement needs a modelling decision (incidence structure or edge
  subdivision) and its own preservation lemmas.

**Estimated Effort**:
- Exploration: 1–3 days (fix the model; decide Approach A vs B; inventory which
  parent lemmas port directly).
- If tractable: 1–2 weeks for the `SimpleGraph` sufficiency theorem plus the
  trail corollary.
- If hard: multigraph faithfulness and the directed→undirected descent could
  extend this if the dart pairing resists formalization.

## References

### Papers
- L. Euler, "Solutio problematis ad geometriam situs pertinentis,"
  *Commentarii Academiae Scientiarum Petropolitanae* 8 (1736), 128–140 — the
  Königsberg bridges paper; origin of graph theory and the degree-parity
  argument.
- C. Hierholzer, "Über die Möglichkeit, einen Linienzug ohne Wiederholung und
  ohne Unterbrechung zu umfahren," *Mathematische Annalen* 6 (1873), 30–32 —
  the constructive circuit-splicing algorithm (published posthumously).

### Books
- R. Diestel, *Graph Theory*, 5th ed., Springer GTM 173 — Chapter 1 covers
  Eulerian tours and Euler's theorem for the undirected/multigraph case.
- D. B. West, *Introduction to Graph Theory*, 2nd ed. — Theorem 1.2.26
  (Eulerian circuit iff connected and all degrees even), with the trail variant.

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.Trails` — `Walk.IsEulerian`,
  `IsEulerian.isTrail`, `IsEulerian.even_degree_iff` (necessity direction),
  `IsEulerian.card_odd_degree`, `IsTrail.even_countP_edges_iff`,
  `IsTrail.isEulerian_iff`.
- `Mathlib.Combinatorics.SimpleGraph.Walk` / `.Path` — `Walk`, `IsTrail`,
  `IsCircuit`, `edges`, `edgeSet`, walk append/concatenation API.
- `Mathlib.Combinatorics.SimpleGraph.Connectivity` — `Connected`, `Reachable`,
  `Preconnected` for the connectivity hypotheses.
- `Mathlib.Combinatorics.SimpleGraph.DegreeSum` — degree sum / handshake lemma
  giving that the number of odd-degree vertices is even.

## Metadata

```yaml
tags:
  - combinatorics
  - graph-theory
  - euler-paths
  - konigsberg
  - hierholzer
related_proofs:
  - konigsberg-oq-02-oq-01
  - konigsberg-oq-02
  - konigsberg
difficulty: high
source: gallery-gap
created: 2026-06-30T22:49:26-07:00
```
