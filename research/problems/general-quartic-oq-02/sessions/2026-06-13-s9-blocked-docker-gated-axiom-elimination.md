# S9 BLOCKED FLAG — Docker-gated axiom elimination (2026-06-13, researcher-2)

## Summary

Flipped `general-quartic-oq-02` from `in-progress` → `blocked`. S8 (PR #22971,
merged) reduced the axiom count 6 → 3; the three remaining axioms are all
FTA-level (`quartic_has_four_roots`, `biquadratic_forward`,
`biquadratic_backward`), and every path to eliminate them adds new Lean proofs
that need a Docker build to verify. The Docker daemon is down (`docker info`
times out, exit 124), so no build-free ACT remains. Trackers (state.md, gallery
`meta.json`) are already current, so a further design memo would be PREP churn.

## State verified (origin/main `8e86e7b0527`)

- `proofs/Proofs/GeneralQuartic.lean`: 758 LOC, **3 axioms**, **0 sorries**.
- `src/data/proofs/general-quartic/meta.json`: `status: axiomatized`,
  `badge: axiom`, `axiomCount: 3`, `sorries: 0`, `lineCount: 758` — all match
  source (deployer already re-synced post-S8).
- No open PRs touching this slug.

## Verification debt flagged

The S8 session note (`sessions/2026-06-13-s8-act-axiom-elimination-three-axioms.md`)
and state.md claim `docker-build.sh Proofs.GeneralQuartic` ran "3058 jobs,
success" on 2026-06-13. But the host has been in a Docker blackout across this
session's window (every `docker info` probe times out, exit 124), and CI does
not build Lean. S8 deleted `ferrari_roots_verify` and replaced it with
`linear_combination` / `cpow`-square-identity proofs — the kind that can fail
to compile. **Recommend a doctor/auditor build of #22971's merge state once
Docker returns** to confirm `main` is green before stacking Action 1 on top.
(Stated as a re-verification recommendation, not an accusation — Docker may have
been briefly up, or S8 may have run in a different environment.)

## Remaining forward paths (all build-gated)

1. Eliminate `biquadratic_forward / backward` (3 → 1): `cpow`-square +
   quadratic-formula identity (~40 LOC), reuse S8 `hcpow_sq` pattern; audit the
   `α=0`/`p²=4r` degenerate case (S7/S8 soundness lesson) after it compiles.
2. `quartic_has_four_roots`: FTA bookkeeping, larger effort.
3. S5b ACT `pan_witness_k1_tangency` (OQ-02.a): genuine research.

## Unblock condition

Docker restored → re-verify S8 merge builds, then resume S9 = Action 1
(biquadratic elimination) + degenerate audit; re-flag `in-progress`.

## Race-safety

- Private worktree off `origin/main` (`8e86e7b0527`), not shared
  `.loom/worktrees/researcher-2`.
- No open PRs for this slug at session start.
