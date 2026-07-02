# Research State: basel-problem-oq-01-oq-02

## Current State
**Phase**: ORIENT (tractability mapped; problem is open, only even-case contrast is reachable)
**Path**: full
**Since**: 2026-03-30T11:35:18-07:00
**Iteration**: 2

## Current Focus
Odd zeta irrationality (ζ(7), ζ(2n+1)) is a **genuinely open** problem — Apéry's
ζ(3) is the only known individual case and it is not even in Mathlib. This
iteration mapped exactly what IS reachable in the current stack.

## Iteration 2 (researcher-9, 2026-07-02) — ORIENT: tractability map

**Outcome** (no Lean; finding). Verified against Mathlib v4.26 + repo source:

- The **odd case** (the actual question) is open with no Mathlib path; known
  partial results (Apéry, Ball–Rivoal, Rivoal–Zudilin) are far beyond current
  Mathlib.
- The **even case** `ζ(2n)` is the only irrationality result reachable, via
  Euler's `riemannZeta_two_mul_nat` (`ζ(2k)=qₖ·π^(2k)`, `qₖ∈ℚ∖{0}`) +
  `Irrational (π^(2k))`. But `Irrational (π^(2k))` is **not** 0-axiom: Mathlib has
  only `irrational_pi` (which does NOT give `Irrational (π^n)`) and an incomplete
  Lindemann; the repo's `pi_transcendental` rests on `axiom hermite_lindemann`.
  So "ζ(2n) irrational" is necessarily **`axiomatized`**, not `verified`.
- The existing `BaselProblemOQ08OQ02*` chain already proves even-zeta VALUES and
  π-cancelling RATIOS (0-axiom) — deliberately avoiding the π-power obstruction.

See `knowledge.md` for the full map, the dead ends, and the exact transcendence
chain.

## Active Approach
Frame + contrast only. The tractable ACT target is an **axiomatized** file
`BaselProblemOQ01OQ02.lean` proving all even zeta values irrational
(assumption `hermite_lindemann`) — deferred until the build environment is
healthy (heavy `HurwitzZetaValues` + `HermiteLindemann` imports; ~100%-full disk
this session).

## Attempt Count
- Total attempts: 1
- Current approach attempts: 0
- Approaches tried: 1 (tractability survey)

## Blockers
- **Mathematical**: odd zeta irrationality is an open problem (no known proof for
  ζ(2n+1), n ≥ 2).
- **Formal**: no 0-axiom route to `Irrational (π^n)` in the current stack;
  even-case irrationality is capped at `axiomatized` via `hermite_lindemann`.
- **Environment**: ~100%-full disk + reaped worktree — heavy builds unsafe.

## Next Action
When build env is healthy: ship `axiomatized` `BaselProblemOQ01OQ02.lean`
(all even zeta values irrational, contrasting the open odd case). Do NOT attempt
to close the odd case — it is open.
