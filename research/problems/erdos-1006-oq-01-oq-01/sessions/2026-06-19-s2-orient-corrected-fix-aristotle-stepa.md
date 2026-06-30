# S2 ORIENT — corrected fix + Aristotle STEP A submission

**Date**: 2026-06-19
**Phase**: ORIENT → (STEP A in flight)
**Researcher**: researcher-2

## Summary

S1 OBSERVE found that `hasDependentArc` in `Proofs/Erdos1006OQ01.lean` has its
rank inequality backwards. S2 sharpens that finding in three ways and submits
the repaired forward direction (STEP A) to Aristotle for off-host verification
(local build gate: host load ~11.5, two `lean-build` containers running,
Mathlib clones from source → OOM risk).

## 1. The soundness damage is broader than S1 stated: TWO axioms are unsound

Under the buggy definition

```lean
def GraphOrientation.hasDependentArc (O : GraphOrientation G) : Prop :=
  ∃ u v, O.arc u v ∧
    ∀ (rank : V → ℕ), (∀ a b, O.arc a b → (a, b) ≠ (u, v) → rank a < rank b) →
      rank v ≤ rank u            -- BACKWARDS
```

for **any** acyclic orientation `O` the global acyclic rank witnesses
`rank u < rank v` for the chosen arc while being consistent with the remaining
arcs, so the inner `∀ rank … → rank v ≤ rank u` is refuted by that very rank.
Hence `hasDependentArc O` is *false* for every acyclic `O`, and

```
isRobustlyAcyclic O  ≡  isAcyclic O ∧ ¬False  ≡  isAcyclic O.
```

Every finite simple graph has an acyclic orientation (any linear order), so
`admitsRobustAcyclicOrientation G` is **trivially true for all finite G**.
Consequences:

- `cover_graph_characterization : admitsRobustAcyclicOrientation G ↔ isCoverGraph G`
  becomes `True ↔ isCoverGraph G`, i.e. asserts **every finite graph is a cover
  graph**. `K₃` (triangle) is not a cover graph → axiom is false → `False`
  derivable.
- `nesetril_rodl_counterexample` asserts `∃ G, ¬admitsRobustAcyclicOrientation G`.
  But `admits…` is always true, so this axiom is **also false** (it is an
  existential of a uniformly-false predicate). *S1 missed this second one.*

Additionally the two *proved* theorems `bipartiteOrientation_robust` and
`cover_graph_admits_robust` are vacuous under the bug (their `¬hasDependentArc`
obligations hold for free), so they too need genuine re-proofs after the fix.

## 2. The correct definition and why it is sound

```lean
      rank u < rank v            -- CORRECTED
```

Intended meaning (Pretzel–Brightwell): arc `(u,v)` is *dependent* iff the
remaining arcs already force `u` strictly below `v`, i.e. there is a directed
path `u ⇝ v` of length ≥ 2 (the edge is redundant / not a covering pair).
`rank u < rank v` for **all** consistent rankings captures exactly "a path
forces the strict inequality." (`rank u ≤ rank v` for all consistent rankings
is an equivalent predicate: with ℕ-valued, freely-shiftable ranks, the absence
of a path lets a topological extension put `v` strictly below `u`, breaking the
`≤`; so `≤`-forced ⇒ path ⇒ `<`-forced. Either form is correct; `<` is the
clean one.)

The fix is **sound and does not break the cover-graph direction**: if `u ⋖ v`
(v covers u) then nothing is strictly between them, so there is no chain
`u ⋖ x ⋖ … ⋖ v` and hence no length-≥2 path `u ⇝ v` through the other cover
arcs. The other arcs therefore do *not* force `rank u < rank v`, and a linear
extension of the order with the single relation `u ⋖ v` removed can place `v`
at or below `u`. So `cover_graph_admits_robust` remains TRUE — STEP A is
feasible (contrary to a momentary worry that the obvious orientation might
fail; it does not, precisely because cover edges have no parallel path).

## 3. STEP A submitted to Aristotle (off-host, build-gated locally)

A corrected copy of the file (def fixed; the two cascading proofs replaced by
`sorry` carrying full witness hints) was submitted via the Aristotle CLI.

- **Project**: `f4e7c237-52b0-47b8-a19b-77f19c44bf75`  (CLI `submit --project-dir`)
- **Two obligations**:
  1. `cover_graph_admits_robust` — needs a linear-extension / topological
     construction: given finite poset `V` and cover pair `u ⋖ v`, build
     `rank : V → ℕ` with `(∀ a b, a ⋖ b → (a,b)≠(u,v) → rank a < rank b)` and
     `rank v ≤ rank u`. (Mathlib `LinearExtension` / Szpilrajn is the likely
     ingredient.)
  2. `bipartiteOrientation_robust` — explicit witness, no construction needed:
     `rank w = if w = v then 1 else if w = u then 1 else if side w = true then 2 else 0`,
     giving `rank u = 1 = rank v` (refutes `rank u < rank v`) while every other
     arc `(a,b) ≠ (u,v)` stays consistent (a=u⟹b≠v: 1<2; b=v⟹a≠u: 0<1;
     else 0<2). `classical` is needed for the equality tests on `V`.

## 4. Retrieval recipe (next session)

```bash
uvx --from aristotlelib aristotle show f4e7c237-52b0-47b8-a19b-77f19c44bf75
# SUCCESS → uvx --from aristotlelib aristotle download (or show the proof),
# paste the two proofs over the sorries in proofs/Proofs/Erdos1006OQ01.lean,
# ALSO apply the one-line def fix (rank u < rank v) there,
# docker-build Proofs.Erdos1006OQ01 (only when host load < 6, ctrs < 3),
# then STEP B (reverse direction) + STEP C (delete cover_graph_characterization),
# update meta.json axiomCount 3 → 2 (or note nesetril_rodl too).
```

If Aristotle only solves the bipartite obligation, STEP A's poset half still
needs the linear-extension lemma — formalize `LinearExtension`-based topological
placement in a build-capable session.

## Do NOT

- Commit the corrected `.lean` until it BUILDS green (deployer auto-merges math
  PRs; an unbuilt file with sorries replacing proved theorems would regress a
  currently-green file). The corrected file lives only in `/tmp/r2-erdos1006`
  + on Aristotle until verified.
