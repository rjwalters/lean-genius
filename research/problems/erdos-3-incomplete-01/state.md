# State: erdos-3-incomplete-01

**Phase**: ACT (Roth-number lower bound landed)
**Since**: 2026-07-04
**Attempts**: 3
**Status**: progress

## Current Focus

Structural lower bound on the Roth number, bracketing it with the existing
upper bound. Formalizes the "trivial regime" of Erdős #3.

## Result this iteration (attempt 3)

Two axiom-free, `sorry`-free lemmas added (build: 7743 jobs, verified):

1. **`isAPFree_of_card_lt`** — any finite `S` with `S.card < k` is vacuously
   `k`-AP-free: a genuine `k`-AP has exactly `k` distinct elements
   (`arithProg_card`), so cannot fit in a smaller set. Reusable structural fact.
2. **`rothNumber_ge_min`** — `min (k-1) (N+1) ≤ r_k(N)`: the initial segment
   `{0,…,min(k-1,N+1)-1}` is AP-free and enters the family `r_k(N)` maximises
   over. Together with the existing `rothNumber_le_window` (`r_k(N) ≤ N+1`) this
   *brackets* the Roth number: `min(k-1,N+1) ≤ r_k(N) ≤ N+1`. In particular
   `r_k(N) ≥ k-1` for `N ≥ k-1`, so all of the `o(N/log N)` content lives at
   large `N` — there is never a sub-constant floor to exploit.

## Prior results (attempts 1–2)

1. **Bitrot repair.** Non-compiling file fixed (`ArithProg` via `image`,
   `Decidable` instances, docstrings).
2. **0-axiom reduction proved.** `strong_required_bound_implies_conjecture`:
   `(∀ k≥3, StrongRequiredBound k) → Erdos3Conjecture`, via dyadic blocking +
   convergent p-series (`summable_of_strongBound`). See knowledge.md.

## Blockers

- **Mathematics only:** the original `o(N/log N)` sorry
  (`required_bound_implies_conjecture`) is threshold-critical — as hard as
  Erdős #3 (counterexample profile in knowledge.md). Do NOT attempt directly.
- Erdős #3 itself: open; best Roth bounds far from the needed threshold.

## Next Action

Leave the threshold-critical sorry documented. Remaining shallow follow-ups
(optional): expose `summable_of_strongBound` as a reusable density→convergence
lemma elsewhere, or a small-`k` triviality (`ContainsAP A 0` always;
`ContainsAP A 1 ↔ A.Nonempty`). The environment recipe (external worktree,
`LEAN_MEMORY_LIMIT=16384 LEAN_SKIP_CACHE=true`) is proven to work for this file.

## Attempts

- 1: threshold analysis + StrongBound design (verification deferred — no build).
- 2: repaired non-compiling file; compiled & verified the StrongBound reduction
  (0-axiom, 7743 jobs); memory bump to 16 GB needed (transient SIGBUS at 8 GB).
- 3: added `isAPFree_of_card_lt` + `rothNumber_ge_min` (trivial Roth lower
  bound, brackets `rothNumber_le_window`); 0-axiom, 0-sorry, 7743 jobs verified.
