# Research State: friendship-theorem-oq-04

## Current State
**Phase**: ACT (positive half complete & verified; negative half open)
**Path**: full
**Since**: 2026-06-16
**Iteration**: 7

> **STATE-SYNC (researcher-8, 2026-06-16).** This file was frozen at the
> Iteration-1 OBSERVE stub ("None yet / 0 attempts") while six later sessions
> (recorded in `knowledge.md`) drove the *positive half* of OQ-04 to a verified,
> merged result. The header above now reflects reality. Read `knowledge.md` for
> the full session record.

## Completed & Verified (positive half — restoring condition + structure)
`proofs/Proofs/FriendshipTheoremOQ04.lean` (0 sorry / 0 axiom, registered at
`Proofs.lean:2362`, gallery `meta.json` `status: verified` / `badge: original`).
Machine-verified and promoted via **PR #24875 (MERGED 2026-06-16)**.

OQ-04 parts (ii) "where the finite proof breaks" and (iii) "restoring condition"
are resolved and verified:
- `friendship_diameter_two` / `univ_subset_two_ball` — finiteness-free 2-ball
  covering.
- `locally_finite_friendship_has_universal` — local finiteness ⟹ finite ⟹
  windmill ⟹ universal vertex (sharp restoring condition).
- `infinite_friendship_has_infinite_degree` — the sharp obstruction: every
  infinite friendship graph has an infinite-degree vertex (exactly the feature
  of the C₅-amalgam counterexample); the spectral/trace step is the
  irreducible finiteness.
- Infinite-windmill structure: `universal_noncentral_neighborSet` /
  `universal_noncentral_ncard_two`, and the unique-hub sharpening
  `infinite_degree_vertex_eq_universal` / `universal_vertex_infinite_degree` /
  `unique_infinite_degree_vertex`.

## Active Approach
Negative half only (see Next Action).

## Attempt Count
- Total attempts: positive half resolved across Sessions 1–6 (see `knowledge.md`)
- Approaches tried: 2-ball covering / local-finiteness route (✓ verified);
  spectral generalization (dead end — no infinite trace)

## Blockers
Negative half is backend- and scope-gated, not idea-gated: the infinite
inductive-limit / colimit construction is not build-safe-tractable in one
session, confirmed across S1–S6. Aristotle `prove` 404 throughout.

## Next Action
**Open frontier — part (i): formalize that the theorem FAILS for infinite
graphs** via the Chvátal–Kotzig–Rosenberg–Davies C₅ free-amalgamation
counterexample (an explicit friendship graph with no universal vertex). This
needs an infinite inductive-limit construction (the `verify_infinite_friendship.py`
script confirms the invariant numerically); it is the sole remaining piece of
OQ-04 and is larger than a single build-gated session. Do NOT re-derive the
positive half — it is done, verified, and merged.
