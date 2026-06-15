# Knowledge Base: friendship-theorem-oq-04

**Friendship Theorem for infinite graphs** — where does the finite proof break,
and what extra condition restores the conclusion?

---

## Problem Understanding

Finite Friendship Theorem (Erdős–Rényi–Sós 1966): in a *finite* simple graph in
which every two distinct vertices have **exactly one** common neighbor, some
vertex is adjacent to all others (a "politician"); the graph is a windmill
`W_k` (k triangles sharing a center, `2k+1` vertices).

OQ-04 asks the infinite analogue: pin down (i) that the theorem **fails** for
infinite graphs, (ii) *exactly which step* of the finite proof breaks, and
(iii) what extra hypothesis brings the conclusion back.

The gallery's finite proof (`proofs/Proofs/FriendshipTheorem.lean`) is a clean
two-step reduction:
- `friendship_has_universal_or_regular` (FriendshipTheorem.lean:179) — dichotomy:
  universal vertex **or** the graph is `k`-regular. (A³-commutativity gives
  "non-adjacent ⟹ equal degree"; complement-connectivity propagates it.)
- `friendship_regular_implies_universal` (FriendshipTheorem.lean:193) — the
  **spectral / eigenvalue-integrality** argument forcing `k = 2`.

---

## Insights (Session 1, 2026-06-15 — ORIENT)

### 1. Counterexample exists (theorem fails for infinite graphs)
Chvátal–Kotzig–Rosenberg–Davies (Canad. Math. Bull. 19(4), 1976: *"There are
2^ℵ_α friendship graphs of cardinal ℵ_α"*). Standard construction = **C₅ free
amalgamation**: start from the 5-cycle; repeatedly add a brand-new private
common neighbor to every pair that currently has none. The countable limit is a
friendship graph with **no universal vertex**.

I verified the construction's correctness invariant myself (not just cited):
adding a fresh `w` adjacent to exactly a zero-common-neighbor pair `{u,v}`
**preserves** the "linear" property (no pair has ≥2 common neighbors), because
any other vertex `x` is adjacent to at most one of `{u,v}` (else `x` would
already be a common neighbor of `u,v`, contradicting zero). So every new pair
`{w,x}` gets ≤1. Hence the closure converges to a genuine friendship graph.
`verify_infinite_friendship.py` confirms max-common-neighbors stays = 1 across 4
rounds (|V| up to 3695), the original C₅ vertices reach exactly-one pairwise, and
**max degree strictly grows** `[4,5,13,83]` ⟹ the limit is **locally infinite**.

### 2. Diameter ≤ 2 — the lemma that SURVIVES infinity
For **every** friendship graph (finite or infinite) and any vertex `v`:

    V = {v} ∪ N(v) ∪ ⋃_{x ∈ N(v)} N(x).

Reason: any non-neighbor `u ≠ v` has a unique common neighbor `x` with `v`;
`x ∈ N(v)` and `u ∈ N(x)`. This is purely local — no finiteness used. Verified
on windmills `W_1..W_8` and on the amalgamation graph.

### 3. RESTORING CONDITION = local finiteness (sharp)
From the diameter-2 covering: if **every degree is finite**, then `V` is a finite
union (`N(v)` finite, each `N(x)` finite) of finite sets ⟹ `V` finite ⟹ (by ERS)
windmill ⟹ universal vertex. So:

> **A locally finite friendship graph is finite (a windmill); the obstruction to
> the infinite theorem is *precisely* the existence of an infinite-degree
> vertex.** Every infinite friendship graph has all (or at least one — in fact,
> by the covering, infinitely many) vertices of infinite degree.

This is a *more elementary* route than the spectral argument: it bypasses
eigenvalues entirely (a 2-ball covering bound). Verified the bound
`|V| ≤ 1 + deg(v) + Σ_{x∈N(v)} deg(x)` on `W_1..W_13`.

### 4. WHERE the finite proof breaks (bearer-pinned)
- **Dichotomy** `friendship_has_universal_or_regular`
  (FriendshipTheorem.lean:179): the "non-adjacent ⟹ equal degree" bijection
  survives only as a **cardinality** statement. When degrees are infinite all
  are equal (= ℵ₀), so the dichotomy's "regular" branch becomes *vacuous* — it
  carries no finite arithmetic content. (The C₅-amalgam counterexample is
  neither universal nor regular, so the dichotomy itself is *false* infinitely.)
- **Spectral step** `friendship_regular_implies_universal`
  (FriendshipTheorem.lean:193) — the **hard break**. Its OQ01 engine is entirely
  finite-matrix algebra:
  - `adjMatrix_sq_eq`: `A² = (k-1)I + J` (FriendshipTheoremOQ01.lean:363)
  - `adjMatrix_trace_zero`: `tr A = 0` (OQ01:362)
  - `trace_adjMatrix_sq`: `tr A² = nk` (OQ01:367) — uses finite `n`
  - `k_sub_one_is_perfect_square` (OQ01:328) and `k_eq_two_no_axiom` (OQ01:330):
    integer eigenvalue multiplicities `m₊,m₋` with `k + (m₊−m₋)s = 0` force
    `k−1 = s²` then `k = 2`.
  None of trace, finite multiplicities, or eigenvalue integrality has an infinite
  analogue. This is the irreducible finiteness in the ERS proof.

---

## Lean target (for a future ACT session, build-gated)

The cleanly formalizable infinite-side results, in order of tractability:

1. `friendship_diameter_two`: `∀ v u, u ≠ v → u ∈ N(v) ∨ ∃ x ∈ N(v), u ∈ N(x)`
   — no `[Fintype V]` needed; pure unfolding of `IsFriendshipGraph` + `ncard=1`.
2. `locally_finite_friendship_is_finite`: with `[LocallyFinite G]` (each
   `neighborSet` finite), `Set.Finite (univ : Set V)` via the covering of (1) as
   a finite union of finite sets (`Set.Finite.biUnion`).
3. Corollary: combine (2) with the existing finite `friendship_theorem`
   (needs bridging `Set.Finite` → `Fintype`) to get a universal vertex under
   local finiteness — the "conclusion restored" statement.

(1)+(2) are `< 150` lines and **finiteness-light**; good Aristotle/ACT targets
once the build backend is available.

---

## Session 2 (2026-06-15 — ACT, build-pending)

Transcribed the ORIENT plan into Lean: **`proofs/Proofs/FriendshipTheoremOQ04.lean`**
(new file, namespace `FriendshipTheoremOQ04`, unregistered in `Proofs.lean` while
the build backend is down — registering a possibly-erroring file into the
auto-merged aggregator would break `main` for everyone).

Contents (all spectral-free, finiteness-light):
- `IsFriendshipGraph` — the `ncard (commonNeighbors) = 1` property *without*
  `[Fintype V]`; definitionally equal to `FriendshipTheorem.IsFriendshipGraph`.
- `exists_common_neighbor` — `ncard = 1 ⟹` a witness via `Set.ncard_eq_one`.
- `friendship_diameter_two` — `u ≠ v ⟹ G.Adj v u ∨ ∃ x, G.Adj v x ∧ G.Adj x u`.
- `univ_subset_two_ball` — `univ ⊆ {v} ∪ N(v) ∪ ⋃_{x∈N(v)} N(x)`.
- `univ_finite_of_locallyFinite` / `locally_finite_is_finite` — local finiteness
  `⟹ (univ).Finite ⟹ Finite V`, via `Set.Finite.biUnion` over the covering.
- `locally_finite_friendship_has_universal` — capstone: bridge `Finite → Fintype`
  (`Fintype.ofFinite`), card `≥ 3` from three distinct vertices
  (`Finset.card_eq_three` + `Finset.card_le_univ`), then apply the finite
  `FriendshipTheorem.friendship_theorem`. Coercion of the friendship hypothesis is
  the identity lambda (definitional equality of the two `IsFriendshipGraph`s).

**Verification status**: NOT machine-checked — Docker build host and Aristotle
backend both unavailable this session (Aristotle `prove` returns 404; `docker info`
times out). Proofs were written for high static compile-confidence and audited by
hand against in-repo lemma usages. Names to re-confirm at build time:
`Set.finite_univ_iff`, `Set.univ_eq_empty_iff`, `Set.Finite.biUnion` arity.

This is the **positive half** of OQ-04 (sharp restoring condition). The negative
half (formalizing the C₅-amalgamation infinite counterexample) remains open.

## Dead Ends / Non-starters
- Trying to recover the theorem via *regularity* alone fails: infinite degrees
  are all "equal" as cardinals, so regularity is vacuously satisfiable without a
  universal vertex (the amalgam is a witness).
- The spectral argument has no salvageable infinite generalization (no trace).

---

## References
- P. Erdős, A. Rényi, V. T. Sós, *On a problem of graph theory*, Studia Sci.
  Math. Hungar. 1 (1966).
- V. Chvátal, A. Kotzig, I. G. Rosenberg, R. O. Davies, *There are 2^ℵ_α
  friendship graphs of cardinal ℵ_α*, Canad. Math. Bull. 19(4) (1976) 431–433.
- *Degrees of vertices in a friendship graph*, Canad. Math. Bull. (1976).
