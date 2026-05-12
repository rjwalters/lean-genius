# Current State

**Phase**: OBSERVE (S1 complete, build pending for S2+)
**Since**: 2026-05-12 (S1 SCAFFOLD by researcher-3)
**Iteration**: 1

## Current Focus

S1 (researcher-3, 2026-05-12) — **OBSERVE survey** of OQ-01 of
`lagrange-theorem-oq-02-oq-02`: "Can the class equation be used to
formally prove the Burnside lemma in Lean 4 using only the
infrastructure developed here?"

Survey-only iteration: no Lean code, no gallery entry, just the
research/JSON scaffolding so the next iteration has a clear API
target and theorem decomposition.

## S1 deliverables (this PR)

- `research/problems/lagrange-theorem-oq-02-oq-02-oq-01/problem.md` —
  problem statement, target theorems, decomposition table.
- `research/problems/lagrange-theorem-oq-02-oq-02-oq-01/knowledge.md` —
  full survey: classical statement, parent-file connection,
  Mathlib API names and signatures, axiom-cleanliness check, S2
  decomposition.
- `research/problems/lagrange-theorem-oq-02-oq-02-oq-01/state.md` —
  this file.
- `src/data/research/problems/lagrange-theorem-oq-02-oq-02-oq-01.json`
  — research-state JSON (knowledge score `0 → 14`).

## S1 findings (one-line summary)

* The OQ is Mathlib-API-bound.
  `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group` exists
  in `Mathlib.GroupTheory.GroupAction.Quotient` and proves the
  symmetric form of Burnside's lemma directly. In-tree precedent:
  `proofs/Proofs/BurnsideCountingOQ03OQ03.lean:87`.
* The parent file's "infrastructure" (class equation,
  orbit–stabiliser for conjugation, centre-vs-singleton-orbit) is
  the specialisation of `MulAction`'s general orbit-decomposition
  machinery to the conjugation action. Burnside is the *same*
  machinery applied to an *arbitrary* action.
* The expected resolution is **YES** with ≲ 100 lines of Lean.
* Axiom-cleanliness check passes: the Mathlib API chain only uses
  `Classical.choice` / `propext` / `Quot.sound`, the standard
  Mathlib triple, none added by this file.

## Active Approach

**OBSERVE → ACT → POLISH** sequence:

* **S1 (this iteration, complete)** — OBSERVE. Survey + scaffold.
* **S2 (next)** — ACT: write
  `proofs/Proofs/LagrangeTheoremOQ02OQ02OQ01.lean` (≲ 100 lines)
  with 4 theorems (`burnside_lemma_sum_form`,
  `burnside_lemma_average_form`,
  `conjugation_burnside_form`, `oq01_resolution`) and the gallery
  entry (`src/data/proofs/lagrange-theorem-oq-02-oq-02-oq-01/{meta,annotations,index}`).
  Report `lf.theoremCount`, `lf.axiomCount`, `lf.sorryCount`.
* **S3 (optional polish)** — Cross-reference back into the parent's
  gallery `meta.json` `openQuestions[0]` with `[RESOLVED in oq-01]`.

## Blockers

None. S2 is unblocked — only needs Docker build access
(`./proofs/scripts/docker-build.sh Proofs.LagrangeTheoremOQ02OQ02OQ01`)
or the build-pending merge pattern recently established by
PR #17763 (cantors-theorem-oq-01-oq-03 S2) and PR #17715
(algebraic-numbers-countable-oq-02-oq-04 S1), where Mathlib API
verified by in-tree usage is accepted as evidence in lieu of a full
Docker build.

## Risks

* **Universe polymorphism.** Bundling general
  `(G : Type*) [Group G] [Fintype G]` statements in a single
  `oq01_resolution` may require explicit universe annotations.
  Mitigation: ship monomorphic `Type` version if `Type*` is awkward;
  the OQ doesn't ask for universe-polymorphic generality.
* **Decidability instances.**
  `[DecidableEq (MulAction.orbitRel.Quotient G X)]` may need to be
  an explicit assumption or derived via `Classical`. The Mathlib
  signature carries it; S2 just propagates it.
* **Parallel SCAFFOLD wave on tier-B slugs.** Per
  `feedback_researcher_tier_b_scaffold_wave_2026_05_12.md`, even
  zero-score tier-B slugs are racing within 15–30 min windows. S1
  push includes a pre-push `gh pr list --search` check.

## Next Action (S2)

Write `proofs/Proofs/LagrangeTheoremOQ02OQ02OQ01.lean` per the
`knowledge.md` § 5 decomposition (4 theorems, ≲ 100 lines), plus the
gallery `meta.json`/`annotations.json`/`index.ts` triple. Mark
status `verified` (0 sorries, 0 axioms) on successful build, or
`axiomatized` if `Classical.choice` is counted; the parent file's
`status: verified` convention treats Mathlib's Classical-choice as
ZFC-standard.

## Attempt Counts

- Total attempts: 1 (S1 OBSERVE)
- Current approach attempts: 1 (succeeded — Mathlib API located)
- Approaches tried: 1
