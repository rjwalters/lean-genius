# Research State: godel-incompleteness-wip-01

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-04-27 (researcher-4 audit)
**Iteration**: post-completion

## Current Focus
Pool entry was stale ("OBSERVE / iteration 1") despite the
formalization being complete. This audit reconciles the
candidate-pool with the actual state of the work.

## Active Approach
Non-vacuous axiomatic proof of Gödel's First Incompleteness
Theorem in `Proofs/GodelFirstIncompletenessOQ01.lean` (~271
lines, 5 axioms, 0 sorries). Distinguished from the companion
`GodelIncompleteness.lean` where `Provable := fun _ => False`
makes all theorems vacuously true.

## Built Items
- `Proofs/GodelFirstIncompletenessOQ01.lean` (~271 lines, 5 axioms,
  0 sorries) with genuine non-vacuous proofs of:
  - `G_not_provable` (via D1 + G_self_reference / Diagonal Lemma)
  - `not_neg_G_provable` (via ω-consistency + neg_G_prov_G)
  - `first_incompleteness` (case split on `Complete`)
  - `G_is_undecidable` (corollary)
- Gallery entry `src/data/proofs/godel-first-incompleteness-oq01/`
  with badge `"axiom"`, status `"axiomatized"`.

## The 5 Axioms (Minimal & Independent)
1. `Provable` opaque (not `fun _ => False`)
2. D1 representability
3. `G_self_reference` (Diagonal Lemma)
4. `omega_consistency_G`
5. `neg_G_prov_G`

Removing any one breaks the proof.

## Mathlib Gap
Full formalization (Paulson's Isabelle treatment) requires
~15,000 lines, including:
- First-order arithmetic infrastructure
- Diagonal Lemma for formal provability
- Σ₁⁰-completeness theorem
- Full D1-D2-D3 derivability conditions

None of this is currently in Mathlib. The axiomatic treatment is
the appropriate endpoint for a gallery entry; the alternative
(full formalization) is a multi-month project deserving its own
upstream Mathlib initiative.

## Remaining Open Questions (Tracked, Not Blocking Completion)
- **Rosser improvement**: replace `omega_consistency_G` with mere
  `Consistent` using Rosser's trick (1936). Would reduce the
  strength of the assumption.
- **Second Incompleteness**: tracked separately as
  `Proofs/GodelSecondIncompletenessOQ02.lean` (Löb's theorem with
  D2, D3 derivability conditions).
- **Diagonal Lemma upstream**: consider submitting the Diagonal
  Lemma as a standalone Mathlib contribution.

## Next Action
Mark COMPLETED in candidate-pool.

## Blockers
None — the formalization is at its appropriate endpoint
(axiomatized) given the upstream Mathlib gap.

## Attempt Count
- Total attempts: completed in prior session
- Current approach attempts: N/A (graduated)
