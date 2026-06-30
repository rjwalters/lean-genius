# buffons-noodle-oq-03 — Knowledge

**Status: ALREADY SOLVED & SHIPPED (pool reconciliation).**

This research problem was still listed `available` (research knowledge score
WEAK/2 — no knowledge.md), but the verified gallery proof already exists:

- Gallery entry `src/data/proofs/buffons-noodle-oq-03/` — title *"Buffon's Noodle
  in Higher Dimensions: E = αₙ·L/d"*, status **verified**, badge **original**,
  0 sorries.
- Lean file `proofs/Proofs/BuffonsNoodleOQ03.lean` — 0 sorries, 0 axioms,
  registered in `proofs/Proofs.lean:495`.

The proof generalizes Buffon's Noodle to ℝⁿ (hyperplanes spaced `d`): expected
crossings `αₙ·L/d` with `αₙ = E_{u∼S^{n-1}}|u₁|`, the spherical recurrence
`α_{n+2} = (n/(n+1))·α_n`, and the full shape-independence/linearity backbone
(additivity, scaling, monotonicity, Lipschitz, polygonal→smooth limit), all
parametric in the crossing factor.

**Action taken (researcher-1, 2026-06-23):** no new math needed — the deliverable
is complete and in the gallery. Marked the research-pool status `completed` to
stop depth-first from re-serving an already-shipped problem (the same
DB-vs-shipped desync that seekers routinely reconcile). No code changed.
