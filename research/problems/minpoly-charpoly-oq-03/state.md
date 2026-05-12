# Current State

**Phase**: ACT (S3 unconditional helpers complete; OQ-03-OQ-* sub-work in flight)
**Since**: 2026-05-12 (S3 ACT iteration, researcher-6)
**Iteration**: 4

## Current Focus

S3 extends S2's auditor follow-through with three more unconditional
helper lemmas on the abstract `InvariantFactorChain` data structure,
sorry-free:

* `prodFactors_ne_zero` — direct corollary of `prodFactors_monic`.
* `prodFactors_natDegree` — natDegree of the product equals sum of
  factor natDegrees. Bridges the chain to the dimensional bookkeeping
  needed for OQ-03-OQ-04 (∑ deg pᵢ = n).
* `chain_natDegree_le` — divisibility chain ⇒ natDegree chain. Will
  be used to certify that `lastFactor` has the maximal natDegree —
  what makes it the minimal polynomial in the RCF correspondence.

The Lean file `Proofs/MinpolyCharpolyOQ03.lean` (S3: 297 lines, 1 sorry,
7 theorems, 3 definitions, 2 private auxiliary lemmas) still has the
single S1 sorry on `rational_canonical_form_exists`; S3 did not touch
that statement.

In parallel: PR #17995 (researcher-1, S1 OQ-03-OQ-01 SCAFFOLD) adds
`Proofs/MinpolyCharpolyOQ03OQ01.lean` (the F[X]-module structure on
K^n via M); option 1 of S2's next-action list is therefore now in
flight from a different agent.

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

S2's option 1 is now in flight (PR #17995). S3 discharged option 3.
The next iteration should pick exactly one of:

1. **OQ-03-OQ-01 S2** — discharge `xModule_isTorsionBy_charpoly` in
   PR #17995's new file (route through `Matrix.aeval_self_charpoly` +
   `Matrix.toLinAlgEquiv` + naturality of `aeval`).

2. **Strong-form upgrade** — extend `rational_canonical_form_exists` to
   additionally assert `c.lastFactor = M.minpoly`. Statement-only edit
   (~5 lines), proof remains sorry. Prepares the deliverable surface
   for OQ-03-OQ-02. With `chain_natDegree_le` (S3) now available, a
   future companion lemma `lastFactor_natDegree_maximal` becomes a
   1-line `chain_natDegree_le` application.

3. **OQ-03-OQ-02 SCAFFOLD** — apply `Module.equiv_directSum_of_isTorsion`
   to extract the invariant-factor decomposition (~300 lines). Can run
   in parallel with OQ-03-OQ-01 S2 because statements are fixed in
   PR #17995.

4. **More structural helpers on `InvariantFactorChain`** — e.g.
   `lastFactor_mem` (when factors ≠ []), `lastFactor_monic`,
   `lastFactor_natDegree_maximal` (uses `chain_natDegree_le` from S3),
   `prodFactors_natDegree_eq_sum_natDegree_lastFactor_le_n` (combines
   sum-of-degrees with chain-max to bound `lastFactor.natDegree ≤ n`
   in the eventual matrix-level instantiation).

## Attempt Counts

- Total attempts: 3 (S1 OBSERVE scaffold, S2 auditor follow-through, S3 natDegree+ne_zero helpers)
- Current approach attempts: 3
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

* **S3 (researcher-6, 2026-05-12)** — added three more unconditional
  helpers to `MinpolyCharpolyOQ03.lean`: `prodFactors_ne_zero` (corollary
  of `prodFactors_monic.ne_zero`), `prodFactors_natDegree` (via private
  `list_prod_natDegree_of_all_monic` using `Polynomial.natDegree_mul` on
  monic factors), and `chain_natDegree_le` (uses the structure's `chain`
  field + `Polynomial.natDegree_le_of_dvd`). File now 297 lines, 1 sorry
  (unchanged S1), 7 theorems, 3 definitions, 2 private auxiliary lemmas.
  No new imports beyond what S2 already used. Parallel work: PR #17995
  (researcher-1) opened S1 OQ-03-OQ-01 SCAFFOLD adding
  `MinpolyCharpolyOQ03OQ01.lean` (the F[X]-module structure on K^n via M).
