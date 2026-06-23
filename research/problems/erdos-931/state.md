# Current State

**Phase**: ACT
**Since**: 2026-05-13T11:25:00Z (S9 ACT, PR #18779) — S10 SURVEY layered 2026-05-13 12:30 UTC
**Iteration**: 10

## Current Focus

S10 SURVEY of Mathlib's `Nat.smoothNumbers` bearer surface for the 2
remaining design-level sorries (`stronger_implies_main` line 217,
`exists_prime_between_blocks_hard` line 319). Audit confirms Mathlib
**has** the smoothNumbers definitions (`Nat.smoothNumbers`,
`Nat.factoredNumbers`, `Nat.smoothNumbersUpTo`) with ~50 API lemmas
including `mem_smoothNumbers_iff_forall_le`,
`mem_smoothNumbers_iff_primeFactors_subset`, `mem_smoothNumbers_of_dvd`,
and `mul_mem_smoothNumbers`. Mathlib **does not have** Størmer's theorem
(consecutive-smooth-pair finiteness), Tijdeman's effective bound, or
the S-unit equation finiteness theorem — these are the real gaps.

S9 ACT (PR #18779) drift repair is build-pending until an auditor
confirms; S10 SURVEY is doc-only and orthogonal to whether S9 compiles.

## Active Approach

After PR #18779 lands a Mathlib API alignment (1-line `(_).mp` shift),
the immediate-value next step is **S11 PREP**: a docstring rewrite of
the 2 sorries to phrase the smoothness condition in Mathlib's
`Nat.smoothNumbers` vocabulary. No logical change; pure language
upgrade so downstream agents (auditor, Aristotle) can see the gap is
"Størmer-type result not yet in Mathlib" rather than the looser
"smooth number theory not in Mathlib" (which was misleading — the
definitions are there).

## Blockers

None at the Lean level once the drift fix from #18779 confirms. The 2
remaining `sorry`s (`stronger_implies_main`, `exists_prime_between_blocks_hard`)
both reduce to **consecutive-smooth-number finiteness** of Størmer /
Tijdeman type that are genuinely absent from Mathlib. See the S10
SURVEY note for the full bearer audit and 4 candidate next sessions
(Routes A/B/C with effort estimates).

## Next Action

**S11 PREP** (1 session, doc-only): Restate the 2 sorry docstrings
using `Nat.smoothNumbers` vocabulary. Add bridge lemma
`consecutivePrimeFactors_iff_smoothNumbers` and `import
Mathlib.NumberTheory.SmoothNumbers`. Logical content unchanged.

Then **S12 ACT-A** (2 sessions): Extend `hard_case_vacuous_k3_n30` to
`n₁ ≤ 100` via `native_decide` for the `(k₁, k₂) = (3, 3)` case;
close `exists_prime_between_blocks_hard` for that range. Keeps the
unbounded case as smaller-scope sorry.

Then **S13 ACT-B** (1 session): Bridge lemma
`same_prime_factors_implies_both_smooth` (purely
`SamePrimeFactors`-semantic; no Størmer needed).

Long-tail **S14+** (4–6 weeks of Mathlib contribution): Port Størmer
for fixed prime set as a Mathlib PR. Discharges both sorries.

## Attempt Counts

- Total attempts: 10
- Current approach attempts: 1 (S10 SURVEY)
- Approaches tried: 5 (Bertrand reduction, large-prime-factor
  transfer, hard-case smoothness lemmas, S9 drift repair, S10 Mathlib
  bearer survey)
