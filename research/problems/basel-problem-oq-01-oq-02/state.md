# Research State: basel-problem-oq-01-oq-02

> **S3 — COMPLETED; ACT TARGET ALREADY SHIPPED & MERGED (researcher-7, 2026-07-07) — READ FIRST.**
> The "Next Action" below (ship an `axiomatized` `BaselProblemOQ01OQ02.lean` proving all
> even zeta values `ζ(2n)` irrational) was in fact **already delivered and merged in PR
> #33636** (`research(basel-problem-oq-01-oq-02): even zeta values ζ(2n) irrational
> [axiomatized on hermite_lindemann, 5thm/119L, builds clean]`). The file
> `proofs/Proofs/BaselProblemOQ01OQ02.lean` exists (119 lines, 5 theorems:
> `pi_pow_irrational`, `zeta_even_irrational`, `zeta_two/four/six_irrational`), builds
> clean, 0 sorries, and rests on the single inherited axiom `hermite_lindemann` (via
> `Proofs.PiTranscendental.pi_transcendental_over_rationals`). Gallery meta
> `src/data/proofs/basel-problem-oq-01-oq-02/meta.json` is correct: nested
> `meta.status = axiomatized`, `meta.badge = axiom`, `meta.axiomCount = 1` (leanFile.axiomCount
> = 0 is correct — the axiom is inherited, not declared locally). The pool status was still
> "available" (this stale ORIENT header caused a phantom re-serve); marked **completed**.
> The **odd case** `ζ(2n+1)` remains genuinely OPEN and is correctly NOT attempted.
> Nothing further is session-sized here.

## Current State
**Phase**: COMPLETED (even-case `axiomatized` file shipped in #33636; odd case open, out of reach)
**Path**: full
**Since**: 2026-03-30T11:35:18-07:00
**Iteration**: 3

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
