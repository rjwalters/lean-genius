# Current State

**Phase**: COMPLETED
**Since**: 2026-07-08
**Iteration**: 1

## Current Focus

Erdős #378 is SOLVED and axiomatized honestly (2 deep Granville–Ramaré axioms,
0 sorries). The axiom-independent parity theory of row counts is now complete.

## Active Approach

Involution `k ↦ n − k` on the squarefree-index set. Odd rows: fixed-point-free →
even count (`squarefreeCount_even_of_odd`). Even rows: single fixed point `n/2` →
count odd iff `C(n,n/2)` squarefree (`squarefreeCount_odd_iff_central_squarefree`,
added 2026-07-08).

## Blockers

The two axioms (density existence `η_m`; complement density `< 1`) are the deep
analytic Granville–Ramaré 1996 content — not eliminable from Mathlib without the
full exponential-sum machinery (>>1000 lines). BLOCKED for de-axiomatization.

## Next Action

None high-value. Parity theory complete; density core is the analytic frontier
(out of scope). If re-served, treat as complete.

## Iteration 2 (researcher-6, 2026-07-09) — UNVERIFIED (docker infra down)

Added `odd_squarefreeCount_iff`: the single unified parity characterization
`Odd (squarefreeCount n) ↔ (Even n ∧ 2 ≤ n ∧ Squarefree (C(n, n/2)))`, folding the
odd-row theorem (`squarefreeCount_even_of_odd`) and the even-row theorem
(`squarefreeCount_odd_iff_central_squarefree`) plus the degenerate rows `n = 0, 1`
into one closed criterion for the whole row-count parity sequence. Pure case split on
`Nat.even_or_odd n` + `n < 2` vs `2 ≤ n` (n=0 via `simp [squarefreeCount]` + `decide`).
0-sorry, no new axiom (still the 2 Granville–Ramaré density axioms). Gallery meta
lineCount 403→432, theoremCount 12→13. Docker infra down all session → UNVERIFIED,
hand-audited (parity lemma names confirmed in codebase). The two axioms remain the
out-of-scope analytic frontier.

## Attempt Counts

- Total attempts: 2
- Approaches tried: 1 (involution parity extension)
