# Knowledge Base: mantel-theorem-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

**Headline (OPEN, not in Mathlib).** Erdős–Simonovits stability for the triangle-free
(`K₃`-free) case: any triangle-free graph on `n` vertices with
`|E(G)| ≥ ⌊n²/4⌋ − o(n²)` can be made bipartite (edit-close to
`K_{⌊n/2⌋,⌈n/2⌉}`) by adding/deleting only `o(n²)` edges. This upgrades the *numerical*
extremal bound (`mantel-theorem`, already in the gallery) to a *structural* one.

Two things are genuinely missing and neither is in Mathlib `v4.26.0`:
1. A usable notion of "`o(n²)`-close" — an edit distance between graphs on a shared
   vertex set (symmetric difference of edge sets, `(G.edgeFinset ∆ H.edgeFinset).card`).
2. The stability theorem itself.

---

## Insights

### Standard proof route (degree-cleaning + Andrásfai–Erdős–Sós)

The textbook proof of triangle-free edge-count stability does NOT need the triangle
removal lemma. It goes:

1. **Clean low-degree vertices.** Let `G` be triangle-free with `e(G) ≥ n²/4 − εn²`.
   Repeatedly delete any vertex of degree `≤ (2/5)n`. Each deletion removes `≤ (2/5)n`
   edges. Near-extremality forces the average degree `≈ n/2`, so only `O(εn)` vertices
   can be deleted before the survivor `G'` has minimum degree `> (2/5)|V(G')|`. Total
   edges lost: `o(n²)`.
2. **Apply AES.** Andrásfai–Erdős–Sós (triangle-free case): a triangle-free graph with
   minimum degree `> 2n/5` is bipartite. So the cleaned `G'` is bipartite.
3. **Account.** `G` differs from a bipartite graph (extend `G'`'s bipartition back over
   the deleted vertices arbitrarily) by only the `o(n²)` deleted edges ⇒ stability.

The `> 2n/5` threshold is sharp: the balanced blow-up of `C₅` is triangle-free,
non-bipartite, and has min degree exactly `2n/5`.

### What Mathlib already gives us (the load-bearing lemma)

`SimpleGraph.colorable_of_cliqueFree_lt_minDegree`
(`Mathlib/Combinatorics/SimpleGraph/FiveWheelLike.lean`, Brandt's proof): a `Kᵣ₊₁`-free
graph with `(3r−4)·n/(3r−1) < δ(G)` is `r`-colorable. At `r = 2` the threshold
`(3·2−4)n/(3·2−1)` is literally `2n/5`, giving step 2 above for free.

### Progress so far

- **PR #25255 (OPEN, build-pending orphan)** `proofs/Proofs/MantelStabilityOQ01.lean`:
  packages step 2 as two thin specializations (0 sorries, 0 axioms, UNREGISTERED so no
  false "green"):
  - `triangleFree_colorable_two_of_lt_minDegree` — `K₃`-free ∧ `2·card V/5 < minDegree`
    ⇒ `Colorable 2`. The `r = 2` instance of `colorable_of_cliqueFree_lt_minDegree`;
    threshold collapse discharged by `omega`.
  - `minDegree_le_of_triangleFree_not_colorable_two` — contrapositive (the
    "sparse-at-some-vertex" shape used by the cleaning step).
  Awaits a green Docker build before it can be registered in `Proofs.lean`.

### Next ingredients (in dependency order)

These are the concrete sub-lemmas still to formalize. Each names the *candidate* Mathlib
API to confirm once a build environment is available (names below are from memory and
MUST be re-checked against the pinned checkout `leanprover-community/mathlib4 @
2df2f0150c` before relying on them):

1. **Handshake / edge-count ↔ degree-sum.** `∑ v, G.degree v = 2 · G.edgeFinset.card`.
   Candidate: `SimpleGraph.sum_degrees_eq_twice_card_edges`. Needed to turn the
   edge-count hypothesis into an average-degree statement.
2. **Few low-degree vertices.** From `e(G) ≥ n²/4 − εn²` and handshake: the set
   `{v | G.degree v ≤ 2n/5}` has size `O(εn)`. This is a Markov/averaging bound over the
   degree sequence — pure `Finset` counting, no graph-specific Mathlib API beyond (1).
3. **Edges lost under vertex deletion.** Deleting a vertex set `S` removes
   `≤ ∑_{v∈S} G.degree v` edges. Candidate building blocks: `SimpleGraph.deleteVerts` /
   induced-subgraph edge bounds, or count directly via `edgeFinset` filtered on `S`.
4. **Edit-distance statement.** Define closeness as
   `(G.edgeFinset ∆ H.edgeFinset).card` and assemble 1–3 + PR #25255's AES step into the
   exact-stability corollary first (constant-edge slack ⇒ bipartite), then the
   asymptotic `o(n²)` form.

---

## Dead Ends

- The *exact* extremal form (`mantel-theorem`, `mantel-theorem-uniqueness`) is fully done
  in `proofs/Proofs/MantelTheorem.lean` and `MantelTheoremUniqueness.lean`. Stability is a
  strictly harder, separate result — do not conflate.
- The triangle removal lemma route is also valid but heavier; the degree-cleaning route
  above is preferred because its key step (AES) is already in Mathlib.
- This problem's further Lean progress is currently **verification-gated**: under the
  2026-06-16 infra blackout (Docker daemon wedged, `docker run` rc=124; no Aristotle; no
  offline Mathlib checkout to confirm API names) new orphan lemmas cannot be compiled or
  API-checked, so piling more unbuildable scaffolding on top of PR #25255 was deliberately
  avoided as low-value churn. Resume at "Next ingredient (1)" once a build is available.
