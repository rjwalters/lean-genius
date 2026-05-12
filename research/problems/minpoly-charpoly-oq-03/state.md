# Current State

**Phase**: ACT (S5 bookkeeping bound composing S3 + S4; OQ-03-OQ-* sub-work in flight)
**Since**: 2026-05-12 (S5 ACT iteration, researcher-10)
**Iteration**: 6

## Current Focus

S5 composes S3 `prodFactors_natDegree` (sum-of-degrees identity) with
S4 `lastFactor_natDegree_maximal` (degree maximality) to add the
coarse a-priori upper bound `c.prodFactors.natDegree ≤ c.factors.length *
c.lastFactor.natDegree` on `InvariantFactorChain F`. The abstract
counterpart of the matrix-level bound `deg (charpoly M) ≤ k · deg
(minpoly M)` (where `k = #invariant factors`), useful before the
sharper `deg (charpoly M) = n` instantiation lands at OQ-03-OQ-04.

Two new lemmas:

* `prodFactors_natDegree_le_lastFactor_natDegree_mul` (public) — the
  S5 deliverable, conditional on `c.factors ≠ []`.
* `nat_list_sum_le_length_mul_of_all_le` (private) — supporting
  `Nat`-arithmetic fact: a sum over a list of naturals is bounded by
  the length times any common upper bound. Pure `Nat` induction, no
  `Polynomial` content. Generic in `(l : List ℕ) (M : ℕ)` —
  intentionally reusable beyond the `prodFactors`-vs-`lastFactor`
  use site.

Proof of the headline: `rw [prodFactors_natDegree]` reduces the LHS
to `(c.factors.map (·.natDegree)).sum`; each summand is bounded by
`c.lastFactor.natDegree` via `lastFactor_natDegree_maximal` (S4) on
the inverse `List.mem_map` image; the `Nat` helper then bounds the
sum; `List.length_map` rewrites `(c.factors.map _).length` back to
`c.factors.length`. Six tactic-block lines plus the helper's
explicit induction (10 lines).

Net file change: lineCount 377 → 449 (+72); theoremCount 10 → 11
(+1 public); sorry count unchanged at 1 (the S1 placeholder on
`rational_canonical_form_exists`). No new imports beyond what S2-S4
used. Build pending (Docker cold-build ~45 min per `proofs/.lake`
self-symlink trap; matches S2/S3/S4 build-pending precedent).

S4 (researcher-1, 2026-05-12, PR #18086 merged) extends S3 with three more unconditional `lastFactor`-side helper
lemmas on the abstract `InvariantFactorChain` data structure, sorry-free
(conditional only on `c.factors ≠ []`):

* `lastFactor_mem` — when the chain is nonempty, the last factor is a
  member of the chain (direct via `List.getLast?_eq_getLast` +
  `List.getElem_mem`).
* `lastFactor_monic` — one-line application of the structure's `monic`
  field to `lastFactor_mem`.
* `lastFactor_natDegree_maximal` — every factor's natDegree is at most
  `(lastFactor c).natDegree`. One-line application of S3's
  `chain_natDegree_le` with the last index. Abstract counterpart of
  "`pₖ = minpoly M` has the maximal degree among invariant factors"
  in the eventual RCF correspondence.

These were S3's enumerated "option 4" next-action. A private bridging
lemma `lastFactor_eq_getElem_pred` packages the
`getLast?.getD 1 = factors[length - 1]` identification, isolating the
delicate `Fin`/`Nat` index manipulation behind a single API.

The Lean file `Proofs/MinpolyCharpolyOQ03.lean` is now 377 lines, 1
`by sorry` (unchanged S1 on `rational_canonical_form_exists`), 10
public theorems + 3 private auxiliary lemmas + 3 definitions. No new
imports beyond what S3 used.

In parallel: PR #17995 (S1 OQ-03-OQ-01 SCAFFOLD adding
`Proofs/MinpolyCharpolyOQ03OQ01.lean`) merged 2026-05-12T09:57Z;
option 1 from S3's next-action list has therefore advanced.

## Active Approach

Same three-ingredient plan from S1 OBSERVE:

1. In-tree companion-matrix infrastructure (`CayleyHamiltonReductionOQ02OQ01`).
2. Mathlib's `Module.equiv_directSum_of_isTorsion`.
3. Cyclic-summand-to-companion-block correspondence.

S4+ work still decomposes into four sub-OQs:

* **OQ-03-OQ-01** (~150 lines): F[X]-module structure on K^n via M-action;
  prove finitely generated + torsion.  *(SCAFFOLD landed in PR #17995.)*
* **OQ-03-OQ-02** (~300 lines): apply `Module.equiv_directSum_of_isTorsion`
  to obtain the invariant-factor decomposition with divisibility chain.
* **OQ-03-OQ-03** (~250 lines): cyclic summand ↔ companion block.
* **OQ-03-OQ-04** (~200 lines): global similarity transform assembly.

## Blockers

None at the strategy level. Two minor verification tasks remain
(unchanged from S1):

1. Confirm `Module.equiv_directSum_of_isTorsion` signature in current
   Mathlib (referenced from `CayleyHamiltonMinpolyOQ05OQ01OQ04WIP01.lean`
   line 240 — API surface is in use).
2. Surface-level: extend `rational_canonical_form_exists` statement to
   additionally assert `c.lastFactor = M.minpoly` (option 2 from S1).
   With `lastFactor_natDegree_maximal` (S4) now available, the
   downstream link "M.minpoly has maximal degree among invariant
   factors" becomes a 1-line corollary at the matrix instantiation
   step.

## Next Action

S5 discharged the first bullet of S4's option-4 enumeration
(`prodFactors_natDegree_le_lastFactor_natDegree_mul`). The next
iteration should pick exactly one of:

1. **OQ-03-OQ-01 S2** — discharge `xModule_isTorsionBy_charpoly` in
   PR #17995's now-merged `MinpolyCharpolyOQ03OQ01.lean` (route through
   `Matrix.aeval_self_charpoly` + `Matrix.toLinAlgEquiv` + naturality
   of `aeval`).

2. **Strong-form upgrade** — extend `rational_canonical_form_exists` to
   additionally assert `c.lastFactor = M.minpoly`. Statement-only edit
   (~5 lines), proof remains sorry. Prepares the deliverable surface
   for OQ-03-OQ-02. With S4's `lastFactor_mem`/`lastFactor_monic`/
   `lastFactor_natDegree_maximal` and S5's
   `prodFactors_natDegree_le_lastFactor_natDegree_mul` available, a
   downstream `lastFactor_natDegree_le_charpoly_natDegree` corollary
   is now a short combination of S3's `prodFactors_natDegree` and
   S4's `lastFactor_natDegree_maximal` — or even shorter using the
   S5 coarse bound directly.

3. **OQ-03-OQ-02 SCAFFOLD** — apply `Module.equiv_directSum_of_isTorsion`
   to extract the invariant-factor decomposition (~300 lines). Can run
   in parallel with OQ-03-OQ-01 S2 because statements are fixed in
   PR #17995's file.

4. **More structural helpers on `InvariantFactorChain`** — remaining
   S4-option-4 candidates beyond S5:
   * `prodFactors_natDegree_eq_sum_natDegree_lastFactor_le_n` — combines
     sum-of-degrees with chain-max to bound `lastFactor.natDegree ≤ n`
     in the eventual matrix-level instantiation (requires
     `prodFactors = charpoly M`).
   * `firstFactor`-side mirror lemmas (`firstFactor_mem`,
     `firstFactor_monic`, `firstFactor_natDegree_minimal`,
     `factors.length * firstFactor.natDegree ≤ prodFactors.natDegree`)
     — the dual structural pass; the `getLast?`/`head?` asymmetry of
     `Nat`-subtraction makes the `firstFactor` formulation slightly
     cleaner since no `length - 1` arithmetic is needed.

## Attempt Counts

- Total attempts: 5 (S1 OBSERVE scaffold, S2 auditor follow-through, S3 natDegree+ne_zero helpers, S4 lastFactor helpers, S5 length-times-last bookkeeping bound)
- Current approach attempts: 5
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

* **S4 (researcher-1, 2026-05-12)** — added three more unconditional
  helpers on the `lastFactor`-side (S3's option 4):
  `lastFactor_mem` (`List.getLast?_eq_getLast` + `List.getElem_mem`),
  `lastFactor_monic` (one-line via the chain's `monic` field), and
  `lastFactor_natDegree_maximal` (one-line application of S3's
  `chain_natDegree_le` with `j = length - 1`). Internal bridging lemma
  `lastFactor_eq_getElem_pred` packages
  `getLast?.getD 1 = factors[length - 1]` for nonempty lists. File now
  377 lines, 1 sorry (unchanged S1), 10 public theorems + 3 private
  auxiliary lemmas, 3 definitions. No new imports beyond what S3
  used. Build pending (Docker cold-build ~45 min per `proofs/.lake`
  self-symlink trap; convention: build-pending PRs land per S2/S3
  precedent and a later mechanic pass verifies). PR #18086 merged.
  PR #17995 (S1 OQ-03-OQ-01 SCAFFOLD) merged 2026-05-12T09:57Z;
  option 1 from S3's next-action list has advanced under a different
  agent.

* **S5 (researcher-10, 2026-05-12)** — composed S3
  `prodFactors_natDegree` (sum-of-degrees identity) with S4
  `lastFactor_natDegree_maximal` (degree maximality) into the
  coarse a-priori bound
  `prodFactors_natDegree_le_lastFactor_natDegree_mul`:
  `c.prodFactors.natDegree ≤ c.factors.length * c.lastFactor.natDegree`
  conditional on `c.factors ≠ []`. Discharges S4-option-4 bullet 1.
  Supporting private lemma `nat_list_sum_le_length_mul_of_all_le`
  is a pure-`Nat` induction with no `Polynomial` content (reusable
  beyond the use site). File now 449 lines, 1 sorry (unchanged S1),
  11 public theorems + 4 private auxiliary lemmas, 3 definitions. No
  new imports. Build pending (Docker cold-build ~45 min per
  `proofs/.lake` self-symlink trap; matches S2/S3/S4 build-pending
  precedent).
