# Research State: friendship-theorem-oq-04

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-16
**Iteration**: 8

## Current Focus
Structural characterization of the infinite Friendship Theorem. Positive half (parts
(ii) where the finite proof breaks + (iii) the restoring condition) is DONE & verified
and merged (#24875). Now building finiteness-free structural facts about the negative
half (part (i): the theorem fails for infinite graphs).

## Active Approach
Finiteness-free structural lemmas in `proofs/Proofs/FriendshipTheoremOQ04.lean`
(0 sorry / 0 axiom, registered, Docker-GREEN 7745).

Done so far:
- diameter ≤ 2 covering; local-finiteness ⟹ finiteness (sharp restoring condition);
  `infinite_friendship_has_infinite_degree`; infinite-windmill structure;
  `unique_infinite_degree_vertex` (hub is the unique infinite-degree vertex).
- **NEW (S8):** `nonadjacent_neighborSet_equinum` — regularity (finiteness-free):
  non-adjacent vertices have a `Set.BijOn` between neighbour sets. ⟹ any friendship
  graph without a universal vertex is regular (C₅ counterexample is ℵ₀-regular).

## Attempt Count
- Total attempts: 8
- Approaches tried: covering/finiteness (done), windmill structure (done),
  infinite-degree sharpening (done), regularity bijection (done S8).

## Blockers
- Aristotle: 404 (unavailable) across all recent sessions.
- The negative-half **counterexample construction** (explicit C₅ free-amalgamation
  friendship graph) needs an inductive-limit / colimit build — confirmed
  not-single-session-tractable across S1–S7.

## Next Action
Negative-half construction: formalize the C₅ free-amalgamation counterexample (now known
to be ℵ₀-regular) via an inductive-limit. Multi-session. Status stays in-progress
(positive half done; negative-half existence statement not yet formalized).
