# Research State: lagrange-four-squares-oq-01-oq-03

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-15 (S1, researcher-6 — OBSERVE→ORIENT)
**Iteration**: 1

## Current Focus
The exact count is **Jacobi's four-square theorem**: `r4(n) = 8·Σ_{d|n,4∤d} d`
(ordered, signed quadruples). Verified numerically n=1..120 (durable cert
`verify_jacobi_four_squares.py`, exits 0) against both the divisor-sum form and
the odd/even closed forms (`8·σ(n)` / `24·σ(odd part)`). Convention pinned
(`r4(4)=24`, not the naive `8·σ(4)=56` — the `4∤d` exclusion is load-bearing).

## Active Approach
Formalizability assessment. The general theorem is **BLOCKED** by Mathlib gaps:
Mathlib has four-square *existence* (`Nat.sum_four_squares`) but no *count*; the
two-square count `r2` is also absent; and all three classical proof routes —
weight-2 modular forms (θ⁴∈M₂(Γ₀(4))), Hurwitz-quaternion order arithmetic, and
the elementary Lambert/Liouville method — each need ≫1000 LOC of new number theory.
The one elementary Lean-able reduction is `r4 = r2 ⋆ r2` (Cauchy convolution), but
it bottoms out on the missing `r2` count. Recommended tractable increment: a
computable `Finset.card` definition of `r4` + `native_decide` small-n oracle
(mirrors parent OQ01 and the konigsberg Matrix-Tree base-case oracle PR #24324).

## Attempt Count
- Total attempts: 0 (no Lean built — Docker down)
- Current approach attempts: 0
- Approaches tried: 1 surveyed (Mathlib inventory + 3 proof routes assessed)

## Blockers
- Docker build wrapper down (`docker info` timeout) — cannot compile Lean.
- Aristotle MCP `prove` → "Resource not found" — cannot delegate.
- **General-theorem blocker (math, not infra outage)**: Jacobi's formula needs
  Hurwitz-quaternion orders OR weight-2 modular forms, neither developed in Mathlib.

## Next Action
When a build host returns: implement the small-n `native_decide` oracle
(`r4 n = jacobiCount n` for n ≤ ~30) as a build-pending UNREGISTERED file —
real, checkable, convention-pinning, without overclaiming the blocked general
theorem. Re-run `verify_jacobi_four_squares.py` to re-confirm the arithmetic.
Track Mathlib for any Hurwitz-quaternion or `r2`-count contribution that would
unblock the general proof.
