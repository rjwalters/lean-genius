# Knowledge Base: binary-gcd-oq-01-oq-01

## Problem Understanding

The parent `binary-gcd-oq-01` formalises the *step count* `binaryGcdSteps` of
Stein's Binary GCD under a UNIT-COST model and bounds it by
`2*(log₂ a + log₂ b) + 2` (Lamé-style). That is not the running time: each
reduction step touches every bit of the operands. The open question OQ-01 asks
for the TOTAL COST MODEL — an honest bit-operation count.

## Insights (SOLVED, 2026-07-01, researcher-5)

- **Cost model**: `binaryGcdCost a b` mirrors the 5-branch `binaryGcdSteps`
  recursion but charges `Nat.size a + Nat.size b` (combined bit-length) per
  step instead of 1. Well-founded on `a + b`.
- **Per-step bound** `binaryGcdCost_le_steps_mul_size`:
    `binaryGcdCost a b ≤ binaryGcdSteps a b * (Nat.size a + Nat.size b)`.
  KEY STRUCTURAL FACT: neither operand ever grows along the recursion (halving
  or subtract-smaller keeps values ≤ original), so `Nat.size` (monotone via
  `Nat.size_le_size`) never increases → every step ≤ the first. Proof: fuelled
  strong induction on `a+b`, unfold cost & step recursions in LOCKSTEP, single
  `split_ifs` aligns identical if-trees, one reusable per-branch closer.
  Algebra: `(1 + steps) * S = S + steps * S`.
- **Quadratic bound** `binaryGcdCost_le_quadratic` (a,b>0):
    `binaryGcdCost a b ≤ (2*(log₂a+log₂b)+2) * (log₂a+log₂b+2)`.
  = classical O((log N)²) bit-complexity (Brent 1976, Knuth 4.5.2).
  Bridge: `Nat.size a ≤ log₂ a + 1` via `Nat.size_le` + `Nat.lt_pow_succ_log_self`;
  compose with parent `binaryGcdSteps_le_log`; multiply monotone factors by `gcongr`.
- Worked example: `binaryGcdCost 12 8 = 8+6+4+3+2 = 23` (symbolic, no native_decide).
- VERIFIED 0-axiom, 0 sorries, no native_decide. File `Proofs/BinaryGcdOQ01OQ01.lean`.

## Dead Ends

- Did NOT need the sharp equality `Nat.size a = log₂ a + 1`; the ≤ bound suffices.
