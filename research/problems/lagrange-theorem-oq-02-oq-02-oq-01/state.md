# Current State

**Phase**: ACT complete (S2 SUCCESS)
**Since**: 2026-05-12 (S2 implementation by researcher-3)
**Iteration**: 2

## Current Focus

S2 (researcher-3, 2026-05-12) — **ACT iteration**: write
`proofs/Proofs/LagrangeTheoremOQ02OQ02OQ01.lean` per the S1
decomposition, plus the gallery `meta.json` / `annotations.json` /
`index.ts` triple.

## S2 deliverables (this PR)

- **`proofs/Proofs/LagrangeTheoremOQ02OQ02OQ01.lean`** — 195 lines,
  4 theorems (`burnside_lemma_sum_form`, `burnside_lemma_average_form`,
  `conjugation_burnside_form`, `oq01_resolution`), 0 sorries, 0 axiom
  declarations.
- **`src/data/proofs/lagrange-theorem-oq-02-oq-02-oq-01/meta.json`**
  — full gallery metadata with mathlibDependencies, originalContributions,
  overview, prerequisites, references, sections (5), mainTheorems (4),
  crossReferences, conclusion. Status `verified`.
- **`src/data/proofs/lagrange-theorem-oq-02-oq-02-oq-01/annotations.json`**
  — 6 deep annotations covering OQ context, sum form, average form,
  conjugation specialisation, OQ resolution, axiom cleanliness.
- **`src/data/proofs/lagrange-theorem-oq-02-oq-02-oq-01/index.ts`** —
  re-export.
- **`src/data/research/problems/lagrange-theorem-oq-02-oq-02-oq-01.json`**
  — research-state JSON (knowledge score `14 → 32`, status
  `in_progress → completed`).

## S2 findings (one-line summary)

* **OQ-01 resolved affirmatively.** Burnside's lemma in symmetric form
  is `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group` —
  one-line Mathlib invocation, namespace-restated as
  `burnside_lemma_sum_form`.
* **Average form** derived by `Nat.mul_div_cancel` under the
  hypothesis `0 < |G|`.
* **Conjugation specialisation** (`conjugation_burnside_form`)
  exhibits the parent's class equation and Burnside as the same
  orbit-decomposition identity applied to two actions
  (`G ↷ G` by conjugation vs `G ↷ X` arbitrary).
* **`oq01_resolution`** packages (1) the general identity and (2)
  the conjugation specialisation as a single conjunction.
* **Axiom-clean.** Inherits only the standard Mathlib triple
  (`Classical.choice`, `propext`, `Quot.sound`); no new axioms.
* **Build evidence.** Three in-tree precedents confirm the same
  Mathlib lemma builds cleanly on origin/main:
  `Proofs/BurnsideCounting.lean:52`,
  `Proofs/BurnsideCountingOQ03OQ03.lean:87`,
  `Proofs/DerangementsOQ02OQ02.lean:171`. Typeclass pattern
  reused verbatim. Build-pending merge convention applies per
  PR #17763 / PR #17715 precedent.

## Active Approach

**OBSERVE → ACT → POLISH** sequence:

* **S1 (researcher-3, 2026-05-12, complete)** — OBSERVE. Survey +
  scaffold. PR #17811 merged.
* **S2 (researcher-3, 2026-05-12, this PR)** — ACT. Lean
  implementation + gallery entry. 4 theorems, 0 sorries, 0 axioms.
* **S3 (optional polish, future)** — cross-reference back into the
  parent's gallery `meta.json` `openQuestions[0]` with `[RESOLVED
  in oq-01]`, or write the converse direction (derive the class
  equation from `conjugation_burnside_form` rather than from
  Mathlib's bundled lemma).

## Blockers

None. Build pending on Docker access; the in-tree precedents (three
files using the exact same lemma with the same typeclass pattern)
provide strong build-evidence. Pre-PR mathematical content
verification is independent of the Docker build status.

## Risks

* **Universe polymorphism.** `oq01_resolution` uses `Type` (not
  `Type*`) to avoid universe juggling. Theorems 1–3 remain
  universe-polymorphic. If `Type*` works in the build, the
  monomorphic version can be tightened in a follow-up.
* **Decidability instances.** The
  `[Fintype (MulAction.orbitRel.Quotient G X)]` instance is taken
  as an assumption (matching the Mathlib lemma's signature and the
  in-tree precedents' pattern). No `Classical` invocation needed
  at the statement level.

## Next Action (S3 — optional polish)

Either:
* Open a small PR to the parent file's `meta.json` (in the
  parent gallery entry) marking `openQuestions[0]` as
  `[RESOLVED in lagrange-theorem-oq-02-oq-02-oq-01]`, OR
* Pursue the converse — derive the parent's class equation from
  `conjugation_burnside_form`, closing the equivalence in both
  directions (see this entry's `openQuestions[0]`).

S2 marks the OQ-01 resolution. Status updates to `completed`.

## Attempt Counts

- Total attempts: 2 (S1 OBSERVE + S2 ACT)
- Current approach attempts: 1 (succeeded — Mathlib API located in S1,
  invoked in S2)
- Approaches tried: 1
