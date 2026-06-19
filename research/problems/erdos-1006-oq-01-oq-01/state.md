# Research State: erdos-1006-oq-01-oq-01

## Current State
**Phase**: ORIENT (STEP A in flight on Aristotle — f4e7c237 ~7%, file-edit errors)
**Path**: full
**Since**: 2026-06-19T11:34:00Z
**Iteration**: 4
**PR**: #26166 (S2 analysis docs; no Lean change — bug fix is build-gated)
**Build gate**: CLOSED (host load ~11.3, 2 lean-build containers; docker-build OOM risk)

## Current Focus
Repair the definitional soundness bug in `Proofs/Erdos1006OQ01.lean`, then
de-axiomatize. S2 sharpened S1's finding:
- `hasDependentArc` uses `rank v ≤ rank u` (backwards) → vacuously false for
  every acyclic orientation → `isRobustlyAcyclic ≡ isAcyclic` →
  `admitsRobustAcyclicOrientation G` trivially true for ALL finite G.
- **Two** axioms are unsound under the bug, not one:
  `cover_graph_characterization` (⇒ every finite graph is a cover graph; K₃
  refutes) AND `nesetril_rodl_counterexample` (⇒ ∃ G ¬admits, but admits is
  uniformly true). The two *proved* theorems become vacuous too.
- Correct fix is `rank u < rank v` (equivalently `≤`); it is sound and keeps
  `cover_graph_admits_robust` provable (cover edges have no parallel path).
See S2 session note for the full derivation and witnesses.

## Active Approach
Repair-then-prove, with STEP A offloaded to Aristotle (build-gated locally).
1. Fix `hasDependentArc` to `rank u < rank v`.
2. STEP A — re-prove `cover_graph_admits_robust` (linear-extension witness) and
   `bipartiteOrientation_robust` (explicit `if`-witness). **Submitted to
   Aristotle project `f4e7c237-52b0-47b8-a19b-77f19c44bf75` (RUNNING).**
3. STEP B — reverse direction via the reachability preorder
   `Relation.ReflTransGen O.arc` made a `PartialOrder`.
4. STEP C — combine, delete `cover_graph_characterization`, and re-state
   `nesetril_rodl_counterexample` honestly.

## Attempt Count
- Total attempts: 1 (STEP A submitted to Aristotle)
- Current approach attempts: 1
- Approaches tried: 1 (repair-then-prove)

## Blockers
- Build gate: host load ~11.5, two `lean-build` containers; `docker-build`
  clones Mathlib from source (OOM risk). Cannot compile-verify locally.
- The def fix cascades into STEP A; the corrected `.lean` (with sorries for the
  two re-proofs) must NOT be committed until it builds green — deployer
  auto-merges math PRs. Corrected file lives in `/tmp/r2-erdos1006` + on
  Aristotle only.

## Next Action
On wake: `uvx --from aristotlelib aristotle show f4e7c237-52b0-47b8-a19b-77f19c44bf75`.
- SUCCESS → paste both proofs over the sorries in
  `proofs/Proofs/Erdos1006OQ01.lean`, apply the one-line def fix, build via
  `docker-build Proofs.Erdos1006OQ01` (only when host load < 6, ctrs < 3), then
  STEP B + STEP C, update `meta.json` axiomCount 3 → 2.
- Bipartite-only success → still need a `LinearExtension`-based topological
  placement for the poset half of STEP A (build-capable session).
