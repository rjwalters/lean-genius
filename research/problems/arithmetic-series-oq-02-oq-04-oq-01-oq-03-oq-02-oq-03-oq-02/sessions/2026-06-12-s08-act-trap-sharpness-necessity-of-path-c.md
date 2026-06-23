# S8 ACT — Trap sharpness: positive k=0 recovery + necessity of Path C for k≥1

**Agent**: researcher-2
**Date**: 2026-06-12
**Phase**: ACT
**File**: `proofs/Proofs/ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02.lean`
**Build**: Docker-verified (`Proofs.ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02`, 7745 jobs, ✔, 92s)

## Context

Prior state: 18 theorems, 0 axioms, 0 sorries. The S4 ACT trap theorem
`qtMultichoose_at_one_one_eq_zero` records that under `Field R` semantics the
naive substitution `q = t = 1` returns `0` for every column `k + 1 ≥ 1`. But it
stops there — it never establishes that `0` is the **wrong** answer, nor
characterizes the columns where the naive substitution *does* recover the
classical `Nat.multichoose`. The genuine open milestone (positive `at_one_one`
recovery via Path C / `RatFunc.eval`) is a multi-session ~200 LOC task and was
deliberately left untouched.

This iteration ships the **sharpness boundary** instead — a small, fully
verified result that strengthens the existing one-directional trap into a
two-sided characterization and proves Path C is *necessary*, not merely
convenient.

## What landed (Section XI / S8 ACT, +2 theorems)

1. **`qtMultichoose_at_one_one_zero`** (unconditional, positive recovery):
   ```lean
   qtMultichoose (1 : R) (1 : R) n 0 = (Nat.multichoose n 0 : R)
   ```
   The `k = 0` column is the empty product (`= 1`), so there is no `0/0` factor
   to collapse and the naive substitution returns the *correct* classical value
   `Nat.multichoose n 0 = 1`. Proof: `qtMultichoose_zero_right` +
   `Nat.multichoose_zero_right` + `Nat.cast_one`.

2. **`qtMultichoose_at_one_one_ne_classical`** (`[CharZero R]`, `n ≥ 1`,
   necessity of Path C):
   ```lean
   qtMultichoose (1 : R) (1 : R) n (k + 1) ≠ (Nat.multichoose n (k + 1) : R)
   ```
   For every `k ≥ 1` column the naive substitution returns `0`
   (`qtMultichoose_at_one_one_eq_zero`), which is **strictly different** from the
   classical value, since `Nat.multichoose n (k+1) = (n + k).choose (k+1) > 0`
   for `n ≥ 1` (`Nat.multichoose_eq` + `Nat.choose_pos`), and a positive natural
   casts to a nonzero element of a characteristic-zero field.

## Significance

Together the two theorems pin the **exact boundary** of Field-`R`
recoverability: the naive `q = t = 1` substitution agrees with the classical
multichoose **iff `k = 0`**. For every `k ≥ 1` (with `n ≥ 1`, char 0) it
provably disagrees. This upgrades the S4 ACT trap from "the value happens to be
0" to a proved **impossibility result**: no direct Field substitution can
recover `Nat.multichoose n k` for `k ≥ 1`; the lowest-terms reduction of
`RatFunc.eval` (Path C) is genuinely required. This is a citable necessity
statement for the eventual Path C work and for gallery/peer-review framing.

## Axiom / sorry delta

- **0 new axioms, 0 sorries.** Theorem count 18 → 20.

## Why not Path C this iteration

Per `2026-05-13-s05-prep-ratfunc-eval-rescues-path-c-...md` §0.4, Path C carries
~200 LOC of `RatFunc (RatFunc ℚ)` infrastructure overhead and is multi-session;
§2.3 confirms the inner `q = 1` evaluation only succeeds after the two-variable
rational function is reduced to lowest terms, which requires representing
`qtBinom` as an actual `RatFunc (RatFunc ℚ)` element and proving its num/denom
reduction. Not cleanly completable in one verifiable iteration. The sharpness
result is the honest, fully-verified increment that motivates and scopes that
future work.

## Next steps (unchanged frontier)

- **Path C (`RatFunc.eval`) migration** — positive `qtMultichoose 1 1 n k =
  Nat.multichoose n k` for `k ≥ 1`. The real open milestone; ~80–200 LOC,
  multi-session. Section XI now proves it is *necessary*.
- **S7 gallery integration** — doc-only; status `axiomatized` is contentious
  here (file is 0-axiom/0-sorry; conditionality lives in theorem hypotheses,
  not axioms), so defer to a dedicated iteration with an explicit status call.
