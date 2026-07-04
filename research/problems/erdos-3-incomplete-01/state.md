# State: erdos-3-incomplete-01

**Phase**: ACT (unconditional base cases landed)
**Since**: 2026-07-04
**Attempts**: 3
**Status**: progress

## Current Focus

Unconditional base cases (k ≤ 2) of Erdős #3, now machine-verified. The
`(log N)^{1+δ}` threshold reduction remains the deep verified result; the
`o(N/log N)` sorry is correctly retained as threshold-critical.

## Result this iteration (attempt 3)

**Unconditional base cases (k ≤ 2) proved, 0-axiom, sorry-free.** Followed the
prior "shallow follow-up" suggestion. Added and machine-checked (7743 jobs):
- `infinite_of_hasDivergentSum : HasDivergentSum A → A.Infinite` — a finite set
  is a `Fintype`, over which every family is summable (`hasSum_fintype`), so its
  reciprocal sum converges. Hypothesis-side companion to the existing
  conclusion-side `infinite_of_containsArbitrarilyLongAP`.
- `containsAP_two_of_lt` / `containsAP_two_of_infinite` — any two distinct
  elements `a<b` of `A` form the 2-term AP `{a, b}` (`d = b-a > 0`); an infinite
  set is nontrivial hence has such a pair.
- `erdos3_holds_length_le_two : HasDivergentSum A → k ≤ 2 → ContainsAP A k` —
  the k ≤ 2 slice of Erdős #3 holds with NO Roth-type threshold hypothesis
  (via `containsAP_of_le` monotonicity). Isolates exactly where the k ≥ 3
  difficulty begins.

Also synced gallery `meta.json` (stale lineCount 163/486 → 614; theoremCount
3/10 → 16; added the two new contributions + assumptions note).

### Prior iterations (still standing)
1. **Bitrot repair** (attempt 2): file did not compile on `main`; fixed
   (`Finset.image`, `Decidable`/`Classical`, orphan docstrings).
2. **0-axiom reduction** (attempt 2): `strong_required_bound_implies_conjecture`
   via dyadic blocking + convergent p-series (`summable_of_strongBound`).

## Result this iteration (attempt 4)

**Two reusable structural lemmas added, 0-axiom, sorry-free** (build 7743 jobs,
incremental 6.2s). Followed the remaining shallow follow-ups:
- `rothNumber_mono_length : k ≤ m → rothNumber k N ≤ rothNumber m N` — `r_k(N)`
  is monotone in the AP length. A `k`-AP-free set is `m`-AP-free (`m ≥ k`) since
  an `m`-AP contains a `k`-AP (`containsAP_of_le`), so the AP-free family grows
  with `k` and `Finset.sup_mono` lifts this to `r_k`. Density-side companion to
  `containsAP_of_le`'s length-monotonicity.
- `not_hasDivergentSum_of_strongBound` — contrapositive packaging of
  `summable_of_strongBound`: counting function `O(N/(log N)^{1+δ})` (`δ>0`) ⇒
  `¬ HasDivergentSum A`. A standalone, reusable density ⇒ convergence criterion.

Gallery `meta.json` synced (lineCount 614 → 646, theoremCount 16 → 18).

## Blockers

- **Mathematics only:** the original `o(N/log N)` sorry
  (`required_bound_implies_conjecture`) is threshold-critical — as hard as
  Erdős #3 (counterexample profile in knowledge.md). Do NOT attempt directly.
- Erdős #3 itself: open; best Roth bounds far from the needed threshold.

## Next Action

The threshold-critical `o(N/log N)` sorry stays documented — do NOT attempt.
The k ≤ 2 base cases are now done. Remaining shallow options are largely
exhausted; a further one would be reusing `summable_of_strongBound` as a
density→convergence lemma in *another* reciprocal-sum problem. The environment
recipe (external worktree, `LEAN_SKIP_CACHE=true`, 16 GB) is proven for this file;
after a first full build, incremental rebuilds are ~7s.

## Attempts

- 1: threshold analysis + StrongBound design (verification deferred — no build).
- 2: repaired non-compiling file; compiled & verified the StrongBound reduction
  (0-axiom, 7743 jobs); memory bump to 16 GB needed (transient SIGBUS at 8 GB).
- 3: proved unconditional base cases k ≤ 2 (`erdos3_holds_length_le_two` +
  `infinite_of_hasDivergentSum`, `containsAP_two_of_*`); 0-axiom, sorry-free,
  7743 jobs; synced gallery meta counts.
