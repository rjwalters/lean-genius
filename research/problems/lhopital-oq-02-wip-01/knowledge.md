# Knowledge: lhopital-oq-02-wip-01

## Summary

**COMPLETE** — all three target ∞/∞ L'Hôpital variants are fully proven in
`proofs/Proofs/LHopitalOQ02.lean` (0 sorries, 0 axioms). This WIP task was
resolved before it was created: PR #10140 ("prove all 4 ∞/∞ L'Hôpital variants,
0 sorries") landed the complete file, and the Seeker subsequently generated this
redundant completion task on 2026-04-05. Status synced to `completed` on
2026-06-13.

## Session 2026-06-13 (Session 1) — Completion sync

**Mode**: REVISIT
**Outcome**: completed (tracker sync, no new Lean)

### What I Did
- Verified on `origin/main` that `LHopitalOQ02.lean` contains all three target
  theorems fully proven with no `sorry`, `admit`, or `axiom`:
  - `lhopital_infty_left` (line 290) — reduces to `lhopital_infty_right` via the
    negation substitution `u = -x`.
  - `lhopital_infty_atTop` (line 318) — reduces to `lhopital_infty_right` via the
    inversion substitution `u = 1/x`.
  - `lhopital_infty_atBot` (line 353) — reduces to `lhopital_infty_atTop` via the
    negation substitution `u = -x`.
- Traced history: the proofs landed in PR #10140, predating this task. The
  knowledge note's "3 sorries at lines 291, 302, 313" was a planning snapshot
  that never matched the merged file.
- Flipped research JSON `OBSERVE/active` → `COMPLETED/completed` and updated
  `problem.md` status.

### Note
File is not Docker-rebuilt this session (verification blackout). The proofs have
been on `main` since #10140; standard post-blackout re-verification still applies
to the whole gallery.

## Key Facts

- Source file: `proofs/Proofs/LHopitalOQ02.lean` (note: capital H in filename)
- 3 sorries at lines 291, 302, 313: `lhopital_infty_left`, `lhopital_infty_atTop`, `lhopital_infty_atBot`
- All three reduce to the proved `lhopital_infty_right` via variable substitution
- Each substitution: u = a+b-x (reflection), u = 1/x (inversion), u = -x (negation)
- `lhopital_infty_right` is fully proved via `lhopital_infty_right_zero` helper (c=0 case)
- Companion file `LHopitalOQ02Aristotle.lean` already exists — may have supporting lemmas
- Key Mathlib tools: `HasDerivAt.comp`, `HasDerivAt.neg`, filter transformation lemmas

## Open Questions

1. Which exact Mathlib lemmas handle `nhdsWithin` under affine/invertible maps?
2. Does `Mathlib.Analysis.Calculus.LHopital` provide shortcuts we can invoke?
3. For `atTop → right`: does Mathlib have `Filter.tendsto_inv_atTop_nhds_nhdsWithin_zero`?
4. For `atBot → atTop`: `Filter.tendsto_neg_atTop_atBot` (or `atBot_neg`) should handle the filter push.
