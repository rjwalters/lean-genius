# State: erdos-3-incomplete-01

**Phase**: PARTIAL (finding + verified design)
**Since**: 2026-07-02
**Attempts**: 1
**Status**: available

## Current Focus

The sorry `required_bound_implies_conjecture` in `Proofs/Erdos3Problem.lean`.

## Finding

The sorry's hypothesis `RequiredBound k = r_k(N) = o(N/log N)` is the WRONG
threshold: the reciprocal-sum reduction fails at `o(N/log N)` (counting function
`~ N/(log N·loglog N)` is `o(N/log N)` yet has divergent reciprocal sum). As
written the sorry is as hard as Erdős #3 — not a mechanical implication. The file
header's "equivalent to `o(N/log N)`" claim is over-strong. Details + counterexample
in knowledge.md.

## Constructive design (0-axiom, provable)

Add `StrongBound k := ∃ε>0, ∃C, ∀ᶠ N, r_k(N) ≤ C·N/(log N)^{1+ε}` and
`strong_bound_implies_conjecture`, proved by dyadic blocking of `∑ 1/a` into a
convergent p-series `∑ 1/(j+1)^{1+ε}`. Full proof sketch + Mathlib API in
knowledge.md.

## Blockers

1. **Environment (this iteration):** no Mathlib olean cache in the repo; disk at
   99%; worktrees reaped under disk pressure. No `import Mathlib` build could run,
   so the `StrongBound` reduction was designed but not compiled/verified.
2. **Mathematics:** the original `o(N/log N)` sorry is as hard as Erdős #3
   (blocked); Erdős #3 open; best Roth bounds far from the needed threshold.

## Next Action

When a Mathlib build is available: add `StrongBound` + `strong_bound_implies_conjecture`
to `Erdos3Problem.lean` (or a companion `Erdos3StrongBound.lean`), verify 0-axiom
via `lake env lean`, and correct the header's "equivalent to o(N/log N)" wording.
Consider filing a mechanic/curator note to re-label the original sorry as
threshold-critical rather than a tractable logical step.

## Attempts

- 1: threshold analysis + StrongBound design (this iteration; verification deferred
  on environment).
