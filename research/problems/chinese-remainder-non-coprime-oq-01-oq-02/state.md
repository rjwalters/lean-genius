# Research State: chinese-remainder-non-coprime-oq-01-oq-02

## Current State
**Phase**: COMPLETE
**Path**: full
**Since**: 2026-07-24
**Iteration**: 3
**Status**: completed (full Garner algorithm formalized, Docker-verified, 0 sorries / 0 axioms)

## Current Focus
Done. The 2026-06-13 plan (survey iteration 2) was executed verbatim once the
Docker blackout lifted: `proofs/Proofs/ChineseRemainderNonCoprimeOQ01OQ02.lean`
(515 lines, 33 theorems, 11 defs, 5 kernel-`decide` examples) implements and
verifies the complete k-modulus Garner algorithm plus the k(k−1)/2
operation-count bound. Built clean via
`./proofs/scripts/docker-build.sh Proofs.ChineseRemainderNonCoprimeOQ01OQ02`
(8576 jobs, exit 0) on Mathlib v4.31.0.

## Final Approach (as executed)
- `modInv` — executable extended-gcd inverse; correctness in `ZMod m` from
  `Nat.gcd_eq_gcd_ab` (`modInv_zmod`).
- `toDigits`/`ofDigits` — k-modulus mixed-radix representation: round-trip,
  `Forall₂` digit bounds, uniqueness (`digits_unique`), existence
  (`mixed_radix_exists`). Parent's `garner_mixed_radix` = k = 2 case.
- `garner` — forward substitution over `List (ℕ × ℕ)` threading partial
  solution x and processed product P; step digit in truncation-safe ℕ form.
  Deviation from the June plan: instead of proving the Horner/substitution
  telescoping identity, correctness uses an incremental 3-invariant induction
  (`garnerRec_spec`: size, mod-P persistence, new congruence), with the step
  congruence closed by `linear_combination` in `ZMod m` (`nextDigit_step`).
  Strictly simpler; no inverse products ever accumulate.
- `garner_correct` / `garner_unique` — main deliverables; uniqueness via
  `modEq_prod` + `Nat.modEq_and_modEq_iff_modEq_mul`.
- `garnerRec_eq_ofDigits` / `toDigits_garner` — the algorithm's digit stream
  IS the mixed-radix decomposition of its output.
- `stepOps`/`garnerOps_eq` — operation counter with proved closed form
  k(k−1)/2 (`Finset.sum_range_id`), per-step charge grounded by the reduced
  Horner inner loop `hornerMod` (`hornerMod_lt`, `hornerMod_modEq`).

## Attempt Count
- Total attempts: 1 Lean implementation (this session) after 1 paper survey
- Approaches tried: 1 (incremental-invariant induction; worked first time —
  3 minor lemma-name fixes on first compile, then clean)

## Blockers
None. (Historical: 2026-06-13 Docker/Aristotle blackout — resolved.)

## Session Notes (2026-07-24)
- Worktree was janitor-reaped mid-session before first commit (known gotcha);
  recovered by re-creating the worktree on the surviving branch and committing
  immediately. The in-progress Lean file survived.
- Gallery entry created: `src/data/proofs/chinese-remainder-non-coprime-oq-01-oq-02/`
  (meta.json + annotations.json), status `verified`, badge `original`,
  axiomCount 0 (no native_decide — examples use kernel `decide` via
  `garner_unique` to avoid kernel-reducing `Nat.gcdA`).

## Next Action
None — problem closed. Possible follow-ups recorded in the gallery entry's
`conclusion.openQuestions` (amortized inverse-precompute accounting; non-coprime
compatible extension via lcm merging; bit-complexity comparison vs Lagrange CRT).
