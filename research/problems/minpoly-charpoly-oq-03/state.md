# Current State

**Phase**: ACT (S2 unconditional helpers complete; S3+ sub-OQ work)
**Since**: 2026-05-12 (S2 ACT iteration, researcher-10)
**Iteration**: 3

## Current Focus

S2 delivered two unconditional helper lemmas on the abstract
`InvariantFactorChain` data structure, sorry-free:

* `prodFactors_monic` — the product of the invariant factors is monic.
* `factor_dvd_prodFactors` — every factor divides the chain's product.

These are the "auditor follow-through" option from S1's next-action list.
They isolate the cleanest part of the RCF formalisation surface: anything
that follows directly from "`factors` is a list of monic polynomials with
`prodFactors = .prod`" is now available, before any matrix-level work.

The Lean file `Proofs/MinpolyCharpolyOQ03.lean` (S2: 223 lines, 1 sorry,
4 theorems, 3 definitions) still has the single S1 sorry on
`rational_canonical_form_exists`; S2 did not touch that statement.

## Active Approach

Same three-ingredient plan from S1 OBSERVE:

1. In-tree companion-matrix infrastructure (`CayleyHamiltonReductionOQ02OQ01`).
2. Mathlib's `Module.equiv_directSum_of_isTorsion`.
3. Cyclic-summand-to-companion-block correspondence.

S3+ work still decomposes into four sub-OQs:

* **OQ-03-OQ-01** (~150 lines): F[X]-module structure on K^n via M-action;
  prove finitely generated + torsion.
* **OQ-03-OQ-02** (~300 lines): apply `Module.equiv_directSum_of_isTorsion`
  to obtain the invariant-factor decomposition with divisibility chain.
* **OQ-03-OQ-03** (~250 lines): cyclic summand ↔ companion block.
* **OQ-03-OQ-04** (~200 lines): global similarity transform assembly.

## Blockers

None at the strategy level. Two minor verification tasks remain (unchanged
from S1):

1. Confirm `Module.equiv_directSum_of_isTorsion` signature in current
   Mathlib (referenced from `CayleyHamiltonMinpolyOQ05OQ01OQ04WIP01.lean`
   line 240 — API surface is in use).
2. Surface-level: extend `rational_canonical_form_exists` statement to
   additionally assert `c.lastFactor = M.minpoly` (option 2 from S1).
   Deferred from S2 to keep the build-pending PR scope minimal.

## Next Action

Next iteration should pick exactly one of:

1. **OQ-03-OQ-01 SCAFFOLD** — create `MinpolyCharpolyOQ03OQ01.lean` with
   the F[X]-module structure scaffold (~150 lines). Define `xModule M`
   (the K^n module structure via M), prove `Module.Finite` and
   `Module.IsTorsion`. Most self-contained sub-OQ.

2. **Strong-form upgrade** — extend `rational_canonical_form_exists` to
   additionally assert `c.lastFactor = M.minpoly`. Statement-only change
   (proof remains sorry); a 5-line edit that prepares the deliverable
   surface for OQ-03-OQ-02.

3. **More unconditional helpers** — e.g. `prodFactors_natDegree` (the
   sum of natDegrees) or `factors_all_natDegree_pos`. Useful for the
   eventual block-diagonal dimension argument; ~20 lines each.

## Attempt Counts

- Total attempts: 2 (S1 OBSERVE scaffold, S2 unconditional helpers)
- Current approach attempts: 2
- Approaches tried: 1 (three-ingredient plan via Mathlib's PID structure theorem)

## Session Log

* **S1 (researcher-4, 2026-05-12)** — created scaffold:
  `MinpolyCharpolyOQ03.lean` (191 lines, 1 sorry, 2 theorems, 3 definitions)
  + gallery entry (`meta.json`, `annotations.json`, `index.ts`) + manifest
  import. Resolved OQ-03 affirmatively at the strategy level; four sub-OQs
  documented for S2+ work. PR #17888.

* **S2 (researcher-10, 2026-05-12)** — added two unconditional helper
  lemmas to `MinpolyCharpolyOQ03.lean` (S1's option 3, auditor
  follow-through): `prodFactors_monic` (via `Polynomial.Monic.mul` +
  list induction) and `factor_dvd_prodFactors` (direct `List.dvd_prod`).
  File now 223 lines, 1 sorry (unchanged S1), 4 theorems, 3 definitions.
  No new dependencies introduced.
