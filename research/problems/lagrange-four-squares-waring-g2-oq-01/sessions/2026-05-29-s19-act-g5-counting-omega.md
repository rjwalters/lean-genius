# S19 ACT — g(5) ≥ 37 via counting + omega

**Researcher**: researcher-1
**Date**: 2026-05-29
**Mode**: ACT
**PR**: (this PR)

## Summary

Ship the **S5 ACT** Lean deliverable: a sorry-free, axiom-free proof of
`g(5) ≥ 37` via the counting+omega template established by S2b ACT
(PR #18928) and S3 ACT (PR #19129). New file
`proofs/Proofs/LagrangeFourSquaresWaringG2OQ01CountingG5.lean` (146 LOC,
1 theorem `g5_lower_counting`, 0 sorries, 0 axioms).

This is the third instance of the parametric counting+omega template,
extending verified `g(k) ≥ N` coverage from `k ∈ {3, 4}` to
`k ∈ {3, 4, 5}`.

## Why this unblocks despite parent regression

The S17 BUILD-DIAGNOSTIC (2026-05-16) flagged
`proofs/Proofs/LagrangeFourSquares.lean` as v4.26.0-broken with 9
elaboration errors at lines 210–365 — and that file is still broken on
origin/main 13 days later (Mechanic branch `fix/mechanic-lagrange-v426`
applied paste-ready fixes per S18 PREP §3 but was never opened as a PR
or merged).

The S5 ACT bypasses this blocker entirely:

- `LagrangeFourSquaresWaringG2OQ01CountingG5.lean` imports only
  `Mathlib`, same as S3 ACT's `LagrangeFourSquaresWaringG2OQ01CountingG4.lean`.
- No dependency on `Proofs.LagrangeFourSquares` (the broken file).
- No dependency on `Proofs.LagrangeFourSquaresWaringG2` (parent g(2)=4 file).
- The targeted Docker build `Proofs.LagrangeFourSquaresWaringG2OQ01CountingG5`
  succeeds without touching the broken parent.

The path-A-blocking S4 ACT (which DOES need `waringG` from the broken
parent) and the S6 ACT correctness chain remain blocked. But S5 / S6b / S7
ACTs — all routine ports of S3 ACT's recipe at different `k` — are
**parent-independent** and shippable today.

## Build verification

```
./proofs/scripts/docker-build.sh Proofs.LagrangeFourSquaresWaringG2OQ01CountingG5
```

Result (2026-05-29 ~19:25 UTC):

```
✔ [7743/7743] Built Proofs.LagrangeFourSquaresWaringG2OQ01CountingG5 (14s)
Build completed successfully (7743 jobs).
=== Build succeeded ===
```

Fresh Mathlib clone (cache volume populated), build took ~3.5 min wall
clock; the targeted-build pipeline does NOT pull in
`Proofs.LagrangeFourSquares` because `Proofs.LagrangeFourSquaresWaringG2OQ01CountingG5`
has no transitive dependency on it.

Host disk recovered from S18's `7.2 Gi free` to `~51 Gi free` (B2
INFRASTRUCTURE blocker is effectively resolved for targeted builds).

## Mathematical content

**Theorem** `g5_lower_counting : ¬ IsSumOfFifthPowers 36 223`

Combined with the upper-bound axiom `waring_g5_upper` (research-level,
Chen 1964; queued for S4 ACT), this establishes `g(5) = 37`.

**Witness** `223 = 6 · 32 + 31` (six twos contribute `2^5 = 32` each,
plus 31 ones, totaling 37 fifth-powers).

**Proof strategy** (byte-mirroring S3 ACT at `k = 5`):

1. *Bound*: each `f i < 3` since `(f i)^5 ≤ 223 < 243 = 3^5`.
2. *Lift*: `f : Fin 36 → ℕ` becomes `g : Fin 36 → Fin 3`.
3. *Fiber*: `∑ i, ((g i : ℕ))^5 = ∑ k : Fin 3, ((k : ℕ))^5 * n k`
   where `n k := #{i | g i = k}` (via `Finset.sum_fiberwise`).
4. *Partition*: `n 0 + n 1 + n 2 = 36` (via
   `Finset.card_eq_sum_card_fiberwise` + `Fin.sum_univ_three`; uses the
   S2b ACT BUILD-VERIFY `(by simp)` idiom from PR #19041).
5. *Expand*: `Fin.sum_univ_three` gives `n 1 + 32 · n 2 = 223`.
6. *Discharge*: `omega` infeasibility on
   `(n 0 + n 1 + n 2 = 36) ∧ (n 1 + 32·n 2 = 223)`.

Case analysis the omega step covers (S5 PREP boundary table):

| `n 2` | `n 1 = 223 − 32·n 2` | `n 0 = 36 − n 1 − n 2` | Feasibility |
|------:|---------------------:|------------------------:|-------------|
| 0     | 223                  | −188                    | ✗ |
| 1     | 191                  | −156                    | ✗ |
| 2     | 159                  | −125                    | ✗ |
| 3     | 127                  | −94                     | ✗ |
| 4     | 95                   | −63                     | ✗ |
| 5     | 63                   | −32                     | ✗ |
| 6     | 31                   | −1                      | ✗ ("miss by 1") |
| ≥ 7   | ≤ −1                 | —                       | ✗ |

## Files changed

- `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01CountingG5.lean`
  (new, 146 LOC).
- `proofs/Proofs.lean` (+1 import line for new module).
- `research/problems/lagrange-four-squares-waring-g2-oq-01/state.md`
  (S19 ACT entry + iteration counter bump + queued-ACT list refresh).
- `research/problems/lagrange-four-squares-waring-g2-oq-01/sessions/2026-05-29-s19-act-g5-counting-omega.md`
  (this memo).

No `meta.json` edits (slug not yet wired into `src/data/proofs/`; the
upstream gallery entry surfaces `g(2) = 4` only).

## Honesty block

- **Mathematical progress this session**: 1 new theorem
  (`g5_lower_counting`), establishing `g(5) ≥ 37` on origin/main.
- **Build-verification status**: ✅ green at 7743 jobs (targeted Docker
  build, ~3.5 min wall clock with fresh Mathlib clone).
- **Axiom status**: 0 new axioms. The slug's axiom inventory is
  unchanged: S2 ACT still carries `Lean.ofReduceBool` (reflection axiom
  from `native_decide`); S2b ACT, S3 ACT, and now S5 ACT are
  axiom-free.
- **Sorry status**: 0 sorries in new file.
- **Open conjecture status**: `g(5) = 37` (Chen 1964) remains
  upper-bound-axiomatic; this session ships the matching lower bound.
- **Parent dependency**: ✅ none. The broken `LagrangeFourSquares.lean`
  (B1 from S17) does not block this ACT.

## Path forward

After this PR merges, remaining queued ACTs:

1. **S6b ACT** — `g(6) ≥ 73`, routine port to `k = 6` at `n = 703 =
   11·64 + 63`. Same template; ~150 LOC; parent-independent (no
   dependency on broken `LagrangeFourSquares.lean`).
2. **S7 ACT** — `g(7) ≥ 143`, routine port to `k = 7` at `n = 2175 =
   16·128 + 127`. Larger case load (17 branches vs 7 here); ~200 LOC;
   parent-independent.
3. **S4 ACT** — STILL BLOCKED on Mechanic parent fix (uses `waringG`
   from broken `LagrangeFourSquares.lean`).
4. **S6 ACT** — STILL BLOCKED on Mechanic parent fix (correctness chain
   uses parent's `waringG`).

A follow-up STATE-SYNC iteration should refresh the 13-day-stale
state.md fully (B1 status, Mechanic-branch dormant PR, etc.) — this
ACT focuses on shipping Lean code rather than doc-side cleanup.
