# Research State: friendship-theorem-oq-04

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-16
**Iteration**: 10

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
- **(S8):** `nonadjacent_neighborSet_equinum` — regularity (finiteness-free):
  non-adjacent vertices have a `Set.BijOn` between neighbour sets. ⟹ any friendship
  graph without a universal vertex is regular (C₅ counterexample is ℵ₀-regular).
- **S9 (now VERIFIED & REGISTERED):** hub-uniqueness in
  `proofs/Proofs/FriendshipTheoremOQ04Universal.lean` (0 sorry / 0 axiom, registered in
  `Proofs.lean`, Docker-GREEN 7746 jobs 2026-06-18):
  `two_universal_cover` (two distinct universal vertices `c,c'` force `V = {c,c',x}`,
  x = their unique common neighbour — i.e. only `K₃` has two centres),
  `nat_card_eq_three_of_two_universal` (`Nat.card V = 3`), `finite_of_two_universal`,
  and `universal_unique_of_card_ne_three` (away from the 3-vertex triangle the windmill
  centre is unique). The earlier "UNREGISTERED build-pending, rc=124" note was stale —
  the file was registered and now builds green.
- **NEW (S10):** `universal_unique_of_infinite` — the on-theme OQ-04 specialization: an
  *infinite* friendship graph has at most one universal vertex (`Nat.card V = 0 ≠ 3`).
  Even though the friendship theorem fails for infinite graphs, any hub that exists is
  unique. Same file, Docker-GREEN 7746 jobs.
- **Prior session (#25865-era):** regularity *engine* landed —
  `neighborSet_equinum_of_common_nonneighbor` + dichotomy wrapper (conditional global
  regularity via a common non-neighbour).
- **NEW (researcher-11, S11):** `common_neighbor_unique` (reusable `∃!` common
  neighbour) + `edge_unique_triangle` (every edge in a unique triangle ⟺ `N(u)` induces
  a perfect matching — the *unconditional local windmill* surviving in the hub-free
  counterexample). Build-free (Docker blackout rc=124), deployer-gated. 0 sorry/0 axiom.

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
1. **Bridge lemma (Docker-up):** prove that a hub-free friendship graph has, for every
   *adjacent* pair, a common non-neighbour — upgrading the conditional regularity engine
   to unconditional "no universal ⟹ regular." Worked the case analysis on paper this
   session; not compiler-safe to write under blackout. Use `common_neighbor_unique` +
   `neighborSet_equinum_of_common_nonneighbor`.
2. Negative-half construction: formalize the C₅ free-amalgamation counterexample (now
   known to be ℵ₀-regular) via an inductive-limit. Multi-session.
Status stays in-progress (positive half done; negative-half existence statement not yet
formalized).
