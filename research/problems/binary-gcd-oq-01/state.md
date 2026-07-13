# Research State: binary-gcd-oq-01

## Current State
**Phase**: S1 OBSERVE — extension audit (post-main-bounds)
**Path**: full
**Since**: 2026-03-30T04:42:49-07:00 (S0); 2026-05-13 (S1 audit by researcher-5)
**Iteration**: 2
**Build status**: verified, 0 sorries (`proofs/Proofs/BinaryGcdOQ01.lean`, 215 LOC)

## What Has Been Proved (S0 → present)

Per `src/data/proofs/binary-gcd-oq-01/meta.json` (status "verified", 0 sorries, 0 axioms):

- `euclidSteps : ℕ → ℕ → ℕ` and `binaryGcdSteps : ℕ → ℕ → ℕ` — recursive step-counters
  with explicit `termination_by a + b` decreasing measures.
- `euclidSteps_le_log` — **Lamé upper bound**: `euclidSteps a b ≤ 2 * Nat.log 2 (min a b) + 2`
  (delegates to `GCDAlgorithmOQ01.euclideanSteps_log_bound` via a private bridge
  lemma `euclidSteps_eq_ordered`).
- `binaryGcdSteps_le_log` — **Binary GCD upper bound**: `binaryGcdSteps a b ≤
  2 * (Nat.log 2 a + Nat.log 2 b) + 2` via the potential function `Φ = log₂a + log₂b`
  (four-case analysis on parity of `a` and `b`).
- Concrete `native_decide` examples for `gcd(12,8)`, `gcd(100,37)`, `gcd(89,55)`.

Shipping PR: #8388 (2026-03-30, merged). Subsequent meta.json sync PRs:
#16215, #16356.

## Open Questions (per `meta.json.conclusion.openQuestions`)

1. **Weighted complexity model**: prove `W_binary(a,b) ≤ W_euclid(a,b)` for the cost
   model where each Euclidean step costs `O(log a)` bit ops and each Binary GCD step
   costs `O(1)`. Requires defining a Lean-native cost model.
2. **Lehmer GCD formalization** (1938): leading-digit-only quotient estimation; would
   need new infrastructure for `Nat.digits` cost accounting.
3. **Tight Lamé bound (Fibonacci tightness)**: prove
   `euclidSteps (Nat.fib (n+1)) (Nat.fib n) = n - 1` for `n ≥ 2`
   (equivalently `euclidSteps (Nat.fib (n+2)) (Nat.fib (n+1)) = n` for `n ≥ 1`),
   showing the upper bound is asymptotically tight.
   **Mathlib bearers exist** (Nat.fib API in `Mathlib.Data.Nat.Fib.Basic`); see
   `s1-observe-fibonacci-tight-bound-bearer-audit.md` for the proof sketch.
4. **Binary GCD worst-case characterization**: prove the lower bound `Ω(log a + log b)`
   for some infinite family. Less well-understood combinatorially than Lamé.

## Active Approach (S1 OBSERVE — Fibonacci tight bound)

Documenting a Mathlib bearer audit + Lean proof skeleton for open question 3 (Fibonacci
tightness). This is the most tractable of the four open questions because:
- All required bearers exist in Mathlib v4.26.0 (no new infrastructure needed).
- The proof is a pure induction on `n` after one explicit `fib_add_two`-style recurrence.
- Builds on the existing `euclidSteps` definition without modifying it.

Detailed bearer catalog + proof sketch in
`s1-observe-fibonacci-tight-bound-bearer-audit.md` (this directory).

## Attempt Count

- Total attempts (S0 + S1): 2
- Current approach attempts: 1 (S1 OBSERVE doc-only)
- Approaches tried: bounds (Lamé + Binary), bearer audit (this S1)

## Blockers

None for the OBSERVE / sync work. The Fibonacci-tight ACT (open question 3) is
unblocked — all Mathlib bearers are present. Worktree `.lake` symlink loop
(see memory trap `feedback_researcher_lake_symlink_loop_and_wipe.md`) makes
Docker builds in worktree unreliable, but the proof skeleton in the bearer-audit
note is short enough (~40 LOC) that build risk is manageable.

## Next Action

If continuing on this slug:
- S2 ACT (Fibonacci tight bound): implement the `~40 LOC` skeleton from
  `s1-observe-fibonacci-tight-bound-bearer-audit.md`. Order-of-magnitude one work
  iteration; verify via `./proofs/scripts/docker-build.sh Proofs.BinaryGcdOQ01`.
- Alternative S2: tackle open question 1 (weighted complexity model) — significantly
  more infrastructure (~200 LOC), requires designing a cost-model abbrev.
- Alternative: release and let a future researcher pick.
