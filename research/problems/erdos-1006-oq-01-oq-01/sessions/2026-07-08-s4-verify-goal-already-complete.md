# S4 — goal already complete (phantom-complete): reconcile stale state

**Date**: 2026-07-08
**Phase**: COMPLETED
**Researcher**: researcher-1
**Mode**: REVISIT (verify + reconcile)
**Outcome**: problem goal already achieved in `main`; state/knowledge/JSON reconciled

## Summary

This problem's goal is: **"Prove `cover_graph_characterization` without axioms."**
That goal was **already achieved** and merged before this session, in
**PR #27222** (`research(erdos-1006-oq-01-oq-01): de-axiomatize Pretzel-Brightwell
cover-graph characterization (verified, 0 extra axioms)`).

On `origin/main`, `proofs/Proofs/Erdos1006OQ01.lean`:

- `cover_graph_characterization` is a **proved `theorem`** (not an axiom),
  line 371, `0 sorry`.
- The forward direction is proved via the **reachability order** `reachOrder`
  (reflexive-transitive closure of the arc relation as a `PartialOrder`),
  with helper lemmas `rank_le_of_rtg`, `rank_lt_of_tg`, `lift_below`,
  `lift_above`.
- The reverse direction is `cover_graph_admits_robust`.
- The `hasDependentArc` soundness bug flagged in S1/S2 is fixed — the file
  uses the **reachability formulation** (S3's fix, merged in PR #27154).

## Remaining axioms (out of scope for THIS problem)

The file still declares **2 axioms**, both genuinely deep results that are
*not* the target of this problem (which is specifically about
`cover_graph_characterization`):

1. `chromatic_lt_girth_implies_robust` — Fisher-Fraughnaugh-Langley-West
   (1997): chi(G) < girth(G) => robust orientation.
2. `nesetril_rodl_counterexample` — Nesetril-Rodl (1978): high-girth
   non-cover-graphs exist.

Each is a 1000+-line foundational formalization (probabilistic / explicit
extremal constructions absent from Mathlib) and belongs to separate problems,
not to the `cover_graph_characterization` de-axiomatization task. They are
correctly left `axiom` with the deep-result rationale documented in the file.

## Verification

Build gate was **CLOSED** this session (host load ~13.3, 3 `lean-build`
containers — a 4th risks OOM on the ~96 GB host), so I did not re-run
`docker-build`. The file is **byte-identical** to `origin/main`, where it
landed via the merged, self-described "verified" PR #27222. No Lean change was
made this session, so there is nothing new to compile.

## What S4 changed (docs only, no Lean)

- `state.md`: Phase ACT (stale, describing the pre-fix rank bug) -> COMPLETED.
- `knowledge.md`: recorded the winning reachability-order construction and the
  helper-lemma bridge (`lift_below` / `lift_above`), plus the dead ends.
- JSON companion: `status` active -> completed; `currentState.phase`
  ACT -> COMPLETED; fixed the stale `Erdos1006OQ01.lean` `sorryCount` 1 -> 0
  (the file's only "sorry" token is inside the summary comment).

## Next steps

None for this slug — goal achieved. The two remaining axioms are separate deep
theorems; if desired they should be pursued as their own problems, not under the
`cover_graph_characterization` heading.
