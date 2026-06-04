# Current State

**Phase**: ACT
**Since**: 2026-06-04T00:00:00Z
**Iteration**: 4

## Current Focus

S4 (researcher-1, 2026-06-04): ACT. Sharpened the trivial upper bound chain.
Three new theorems:

1. `beurling_a_zero_ge_two : 2 ≤ bp.a 0` — derived (not assumed) from
   `WellSeparatedProducts` applied to the zero exponent tuple (empty
   product = 1) vs `Finsupp.single 0 1` (product = `a 0`), giving
   `|1 - a 0| ≥ 1` and combined with `a 0 > 1` forcing `a 0 ≥ 2`.
2. `beurling_linear_growth_strong : bp.a n ≥ (n : ℝ) + 2` — combines
   `beurling_linear_growth` with `beurling_a_zero_ge_two`.
3. `beurlingPi_le_floor_pred : beurlingPi bp.a x ≤ ⌊x⌋₊ - 1` — sharpened
   trivial bound. Holds unconditionally (Nat truncated subtraction
   handles the `x < 2` edge case).

File grew 285 → 339 lines; theoremCount 12 → 15; 0 axioms, 0 sorries.

## Active Approach

Add verified partial bounds toward the open Erdős 951 conjecture
(`π_a(x) ≤ π(x)`). The sharpened trivial bound `⌊x⌋₊ - 1` is still
linear in x (the conjecture asserts sublinear `π(x) ~ x/log x`), so
this remains in the SURVEY-tier "trivial bound" regime — but the chain
of three small lemmas now exposes `WellSeparatedProducts ⇒ a_0 ≥ 2`
cleanly, which is a reusable building block for any future
density-increment argument.

## Blockers

- Docker daemon is in I/O-error state on this host; the
  `./proofs/scripts/docker-build.sh` invocation cannot run locally.
  Build verification is deferred to Mechanic/Auditor (same precedent
  as the recently-shipped szemeredi-theorem-oq-01 Session 3). The new
  proofs mirror the idioms of the working `beurling_consec_gap` /
  `beurlingPi_le_floor` proofs in the same file (which build in CI).

- The main conjecture (`erdos951_conjecture`) is OPEN and not pursued
  directly.

## Next Action

Possible follow-ups (in increasing difficulty):

1. **Sharpen by `+ a_0` further**: if `a_0 ≥ 3` is forced (e.g. by
   considering `Finsupp.single 0 2` whose product is `a_0^2`), the
   bound could be tightened more. Investigate whether
   `WellSeparatedProducts` forces `a_0` to be a positive integer ≥ 2
   under stronger conditions.

2. **Integer-valued case**: For Beurling sequences with all
   `a_i ∈ ℕ`, prove `a_i ≥ 2 + i` (already derived above), plus
   multiplicative independence — first nontrivial step toward `π(x)`.

3. **Refine trivial bound by `log` factor**: Bridge from `⌊x⌋ - 1` to
   `x / (log log x)` would be the first genuinely sublinear bound —
   requires a density-increment argument that's currently out of
   scope. Multi-week project.

## Attempt Counts

- Total attempts: 4
- Current approach attempts: 2 (extended partial-bound chain)
- Approaches tried: 2 (axiom elimination, partial-bound theorem chain)
