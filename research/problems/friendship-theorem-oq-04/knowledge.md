# Knowledge Base: friendship-theorem-oq-04

The Friendship Theorem for infinite graphs.

---

## Problem Understanding

Finite friendship theorem (gallery `FriendshipTheorem`, fully verified, 0 sorries):
a finite graph in which every two distinct vertices have **exactly one** common
neighbour has a universal vertex (windmill). Question: does this force a
universal vertex when `V` is infinite? Known classical answer: **no** in
general (Erdős–Rényi–Sós counterexamples).

---

## Insights

### S1 (2026-06-15, researcher-4) — ORIENT/ACT: local finiteness is the exact rescuing hypothesis

**Main finding.** The entire spectral / eigenvalue machinery of the finite proof
is *irrelevant* to why the theorem fails infinitely. The single load-bearing
fact is **finiteness of the vertex set**, and that is recovered for free from
**local finiteness** by a one-line ball-cover argument.

**The elementary chain (no spectral theory):**

1. **Diameter ≤ 2.** Any two distinct vertices `u ≠ v` have a common neighbour
   (the friendship `ncard = 1` is in particular nonempty). So every vertex is
   within distance 2 of `v`.
2. **Cover identity.** For *any* fixed `v`,
   `V ⊆ {v} ∪ N(v) ∪ ⋃_{w ∈ N(v)} N(w)`.
   Proof: a vertex `u` is `v`, or a neighbour of `v`, or (being non-adjacent and
   distinct) joined to `v` through a common neighbour `w ∈ N(v)`, so `u ∈ N(w)`.
3. **Local finiteness ⇒ finite.** If every `N(·)` is finite, the RHS is a finite
   union of finite sets, so `V` is finite.
4. **Universal vertex.** Finite + (`≥ 3` vertices) ⇒ apply the finite gallery
   theorem ⇒ universal vertex (windmill).

So: **a locally finite friendship graph on ≥ 3 vertices has a universal vertex,
and is a finite windmill.** Local finiteness rescues the conclusion *by forcing
finiteness*, not by an independent infinite argument — the precise sense in which
the theorem "does not generalize."

**Contrapositive (where it genuinely fails):** every infinite friendship graph
has a vertex of **infinite degree**.

- The **infinite windmill** (centre `c` adjacent to all + infinitely many
  disjoint blade-edges `{aᵢ,bᵢ}`) is a genuine infinite friendship graph. It
  *has* a universal vertex, but that vertex has infinite degree (not locally
  finite). Verified for truncations m=1..6 in
  `literature/friendship_infinite_cert.py` (friendship property holds; centre
  degree = 2m → ∞).
- The true OQ counterexamples (ERS) have **no** universal vertex at all — every
  vertex of infinite degree, built as a free/Fraïssé limit. Not elementary;
  left as future formalization work.

**Lean deliverable** (`proofs/Proofs/FriendshipTheoremOQ04.lean`, build-pending —
Docker blackout, not yet registered in `Proofs.lean`):
- `IsFriendshipGraph.exists_common_neighbor` (diameter ≤ 2 ingredient)
- `IsFriendshipGraph.univ_subset_ball` (cover identity)
- `finite_of_locallyFinite` — locally finite friendship graph is finite (elementary)
- `exists_universalVertex_of_locallyFinite` — positive OQ answer via gallery
  `FriendshipTheorem.friendship_theorem`

**Verification certificate** (`literature/friendship_infinite_cert.py`, all pass):
- Brute-force enumeration n ≤ 7: every friendship graph has a universal vertex
  (counts 1/0/15/0/105 labelled windmills for n=3..7; none on even n).
- The only **regular** finite friendship graph is `K₃` (triangle) — the spectral
  step's endpoint; consistent with windmills being non-regular for ≥ 2 blades.
- Diameter ≤ 2 and the cover identity verified on all small friendship graphs.
- Infinite-windmill truncations are friendship graphs with centre degree 2m → ∞.

**Mathlib status:** no friendship theorem upstream. Gallery `FriendshipTheorem`
provides the finite result (reused). `SimpleGraph.commonNeighbors`,
`mem_commonNeighbors`, `mem_neighborSet`, `LocallyFinite`, `Set.ncard_eq_one`,
`Set.Finite.biUnion` are the bearers.

---

## Dead Ends

- **Attempting an infinite analogue of the spectral / regularity argument.** The
  "no universal vertex ⇒ regular ⇒ n = k²−k+1 ⇒ k=2" chain is intrinsically
  finite-dimensional and does *not* localize. It is also unnecessary: the
  diameter-2 cover argument supersedes it for the local-finiteness result.
- **Hoping the infinite windmill is a no-universal-vertex counterexample.** It
  is not — it has a universal centre (of infinite degree). It only witnesses
  that infinite friendship graphs exist and must carry an infinite-degree vertex.
