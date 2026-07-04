# State: erdos-3-incomplete-01

**Phase**: ACT (verified reduction landed)
**Since**: 2026-07-04
**Attempts**: 2
**Status**: progress

## Current Focus

The `(log N)^{1+δ}` threshold reduction for Erdős #3, now machine-verified.

## Result this iteration

1. **Bitrot repair.** `Proofs/Erdos3Problem.lean` did not compile on `main`
   (enrichment merged without a build): `ArithProg` used `Finset.map` with a
   false `omega` injectivity proof; filters over `Set` membership lacked
   `Decidable` instances; three orphaned `/--` docstrings. Fixed → builds
   cleanly (7743 jobs).
2. **0-axiom reduction proved.** `strong_required_bound_implies_conjecture`:
   `(∀ k≥3, StrongRequiredBound k) → Erdos3Conjecture`, `sorry`-free and
   axiom-free, via dyadic blocking + convergent p-series
   (`summable_of_strongBound`) and the bridge lemma. Plus `containsAP_of_le`
   (length monotonicity). See knowledge.md for the full argument.

## Blockers

- **Mathematics only:** the original `o(N/log N)` sorry
  (`required_bound_implies_conjecture`) is threshold-critical — as hard as
  Erdős #3 (counterexample profile in knowledge.md). Do NOT attempt directly.
- Erdős #3 itself: open; best Roth bounds far from the needed threshold.

## Next Action

Leave the threshold-critical sorry documented. Optional shallow follow-ups:
a `k ≤ 2` triviality corollary, or reusing `summable_of_strongBound` as a
density→convergence lemma elsewhere. The environment recipe (external worktree,
`LEAN_SKIP_CACHE=true`, 16 GB) is proven to work for this file.

## Attempts

- 1: threshold analysis + StrongBound design (verification deferred — no build).
- 2: repaired non-compiling file; compiled & verified the StrongBound reduction
  (0-axiom, 7743 jobs); memory bump to 16 GB needed (transient SIGBUS at 8 GB).
