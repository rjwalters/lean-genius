# Current State

**Phase**: ACT (S1 OBSERVE scaffold complete; S2+ ACT planned for sub-OQs)
**Since**: 2026-05-12 (S1 ACT iteration, researcher-4)
**Iteration**: 2

## Current Focus

S1 OBSERVE scaffold delivered as PR (this session). The parent's third open
question is resolved at the strategy level: the rational canonical form
**is** formalizable in Lean 4, with no genuine Mathlib gap, via a
three-ingredient plan that combines:

1. In-tree companion-matrix infrastructure (`CayleyHamiltonReductionOQ02OQ01`).
2. Mathlib's structure theorem for finitely generated modules over a PID
   (`Module.equiv_directSum_of_isTorsion`).
3. The cyclic-summand-to-companion-block correspondence (one-page argument).

The Lean file `Proofs/MinpolyCharpolyOQ03.lean` contains the
`InvariantFactorChain` data structure, the main theorem statement
`rational_canonical_form_exists` (guarded by a single sorry), and one
unconditional sanity lemma `prodFactors_empty`.

## Active Approach

S2+ work decomposes into four sub-OQs (no implementation in this session):

* **OQ-03-OQ-01** (~150 lines): F[X]-module structure on K^n via M-action;
  prove finitely generated + torsion.
* **OQ-03-OQ-02** (~300 lines): apply `Module.equiv_directSum_of_isTorsion`
  to obtain the invariant-factor decomposition with divisibility chain.
* **OQ-03-OQ-03** (~250 lines): cyclic summand ↔ companion block.
* **OQ-03-OQ-04** (~200 lines): global similarity transform assembly.

## Blockers

None at the strategy level. Two minor S2 verification tasks:

1. Confirm `Module.equiv_directSum_of_isTorsion` signature in current Mathlib
   (referenced from `CayleyHamiltonMinpolyOQ05OQ01OQ04WIP01.lean` line 240 —
   API surface is in use).
2. Confirm `List.prod_nil` definitional reduction for `F[X]` (used by
   `prodFactors_empty`).

## Next Action

Next iteration should pick exactly one of:

1. **OQ-03-OQ-01 SCAFFOLD** — create `MinpolyCharpolyOQ03OQ01.lean` with the
   F[X]-module structure scaffold (~150 lines). Define `xModule M` (the
   K^n module structure via M), prove `Module.Finite` and `Module.IsTorsion`.
   This is the most self-contained sub-OQ and the natural next step.

2. **Strong-form upgrade** — extend `rational_canonical_form_exists` to
   additionally assert `c.lastFactor = M.minpoly`. Statement-only change
   (proof remains sorry); a 5-line edit that prepares the deliverable
   surface for OQ-03-OQ-02.

3. **Auditor follow-through** — add `prodFactors_monic` and
   `factor_dvd_prodFactors` as unconditional helpers (both follow from
   standard List/Monic API). Was scoped out of S1 to keep the scaffold
   minimal; these are clean ~30-line additions that can run independently
   of the four main sub-OQs.

## Attempt Counts

- Total attempts: 1 (S1 OBSERVE scaffold, this session, PR pending)
- Current approach attempts: 1
- Approaches tried: 1 (three-ingredient plan via Mathlib's PID structure theorem)

## Session Log

* **S1 (researcher-4, 2026-05-12)** — created scaffold: `MinpolyCharpolyOQ03.lean`
  (191 lines, 1 sorry, 2 theorems, 3 definitions) + gallery entry
  (`meta.json`, `annotations.json`, `index.ts`) + manifest import. Resolved
  OQ-03 affirmatively at the strategy level; four sub-OQs documented for
  S2+ work.
