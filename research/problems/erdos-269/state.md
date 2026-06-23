# Current State

**Phase**: COMPLETED
**Since**: 2026-03-24T15:15:41Z (registry graduated)
**Iteration**: 6
**Last Updated**: 2026-05-17

## Status Summary

P-smooth LCM Series Irrationality: smooth-numbers infrastructure, LCM
sequence definitions, and the irrationality conjecture itself axiomatized
in three variants (finite P, infinite P, distinct LCM terms). The
underlying Erdős conjecture remains open. Registry graduated 2026-03-24
after PRs #999 (initial), #1978/#2257 (product closure), #5741
(smoothSeq_zero + Mathlib compat); subsequent PRs #7969 and #13317 added
structural theorems and `pow_isPSmooth`. Gallery `meta.json` reflects
current Lean state (303 LOC / 15 thm / 9 def / 3 axiom / 0 sorry,
status `axiomatized`, badge `axiom`).

## Lean File Canonical Counts

`proofs/Proofs/Erdos269Problem.lean` (303 LOC):

| Surface       | Count |
|---------------|-------|
| theorem/lemma | 15    |
| def           | 9     |
| axiom         | 3     |
| sorry         | 0     |

## Axiom Inventory (3)

1. `erdos_269 (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime) (hCard : P.card ≥ 2)` (line 179)
   — The main Erdős conjecture: for finite P with ≥ 2 primes, the LCM
   series sum is irrational.
2. `erdos_269_infinite (P : Set ℕ) (hPrime : ∀ p ∈ P, p.Prime) (hInf : P.Infinite)` (line 205)
   — Infinite-P variant of the conjecture.
3. `erdos_269_distinct (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime) (hCard : P.card ≥ 2)` (line 267)
   — Distinct-LCM-terms variant.

All three axioms encode irreducible mathematical content (the open
conjecture itself + two natural variants).

## Theorem Inventory (15)

P-smooth structural lemmas:
- `one_isPSmooth` (line 53) — 1 is P-smooth for any P
- `prime_isPSmooth` (line 58) — primes in P are P-smooth
- `isPSmooth_mul` (line 67) — product closure (PR #2257)
- `pow_isPSmooth` (line 82) — power closure (PR #13317)

Smooth-sequence + LCM scaffolding:
- `smoothSeq_zero` (line 109) — base case (PR #5741)
- `partialLcm_zero` (line 134) — LCM base case
- `partialLcm_one` (line 138) — LCM successor base
- `partialLcm_succ` (line 142) — LCM recurrence
- `partialLcm_dvd_succ` (line 148) — divisibility of consecutive LCMs
- `smoothSeq_dvd_partialLcm` (line 154) — smooth-sequence divisibility

Equivalence + summary:
- `erdos_269_equivalent` (line 190) — bridges main axiom to series form
- `twoThreeSmooth_card` (line 214) — base demonstration case
- `twoThreeSmooth_prime` (line 217) — primality of the demo case
- `erdos_269_summary` (line 289) — collected summary statement
- `erdos_269_conjecture` (line 299) — top-level conjecture statement
  invoking the main axiom

## Definition Inventory (9)

- `def IsPSmooth` (line 49) — P-smoothness predicate
- `noncomputable def smoothSeq` (line 103) — enumerated P-smooth numbers
- `noncomputable def partialLcm` (line 130) — partial LCM up to index n
- `noncomputable def lcmSeries` (line 168) — the LCM-reciprocal series ℝ
- `def isSeriesRational` (line 187) — rational-series predicate
- `def twoThreeSmooth` (line 211) — {2,3} demonstration P
- `noncomputable def lcmPadicVal` (line 235) — p-adic valuation of LCM
- `def distinctLcmTerms` (line 260) — distinct-LCM-terms set
- `noncomputable def distinctLcmSeries` (line 263) — distinct-LCM series

## Open Conjecture

The Erdős problem itself (irrationality of the P-smooth LCM series for
|P| ≥ 2) remains open. The 3 standing axioms encode the irreducible
mathematical assumptions: any further elimination would require Lean
formalization of an analytic-number-theory irrationality proof, which is
a substantial dedicated project (existing irrationality proofs in the
literature use Padé approximation or Liouville-style estimates, none
currently in Mathlib).

## Blockers

None for the current state. The slug is at its honest rest-state pending
external analytic-NT mathematics.

## Next Action

`COMPLETED` — no further iteration planned without external progress on
the irrationality conjectures. Pool flipped to `completed`; claim
released. Re-open with a SCOPED phase if a relevant Mathlib irrationality
API lands (e.g., Padé approximant infrastructure).

## Attempt Counts

- Total attempts: 6 (iter 1 OBSERVE → iter 2 product closure
  → iter 3 smoothSeq_zero + Mathlib compat → iter 4 structural + sorry
  elimination → iter 5 pow_isPSmooth → iter 6 STATE-SYNC)
- Current approach attempts: 0 (rest state)
- Approaches tried: OBSERVE/enhance, P-smooth-closure-lemmas,
  smoothSeq-scaffolding, structural-theorems, pow-closure, documentation sync

## Iteration Ledger

| Iter | Date       | Phase / Action                                          | PR(s)         |
|------|------------|---------------------------------------------------------|---------------|
| 1    | 2026-01-25 | OBSERVE — initial Lean file w/ enhance + axiom scaffold | #999          |
| 2    | 2026-02-07 | ACT — enhance + product closure (`isPSmooth_mul`)       | #1978, #2257  |
| 3    | 2026-03-24 | ACT — `smoothSeq_zero` + Mathlib 4.26 compat            | #5741         |
| 4    | 2026-03-29 | ACT — structural theorems + sorry elimination           | #7969         |
| 5    | 2026-05-01 | ACT — `pow_isPSmooth` structural lemma                  | #13317        |
| 6    | 2026-05-17 | STATE-SYNC — docs catch up to gallery (registry T-54d)  | (this)        |
