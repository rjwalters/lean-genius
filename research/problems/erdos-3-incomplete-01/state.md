# State: erdos-3-incomplete-01

**Phase**: COMPLETE-EXCEPT-OPEN-CRUX (mature)
**Since**: 2026-07-04
**Attempts**: 6
**Status**: mature — the sole remaining sorry is the open crux; the analytic
Bertrand-boundary toolkit around it is now complete on both threshold axes.

## Result this iteration (attempt 6, 2026-07-09) — UNVERIFIED (docker infra down)

Added `not_summable_one_div_nat_mul_log_mul_const` to `Erdos3LogHarmonic.lean`:
for every `c > 0`, `∑ 1/(n·log(n·c))` **diverges**. This is the exact `p = 1`
divergence twin of the already-verified convergent
`summable_one_div_nat_mul_log_mul_const` (`p = 1+δ`) — together they pin the
constant-in-log Bertrand boundary at the exponent `p = 1`, exactly as
`not_summable_one_div_nat_mul_log` / `summable_one_div_nat_mul_log_rpow` do for
the constant-free (`c = 1`) series. Proof is a tail comparison (mirror of the
convergent lemma's): on `n ≥ max c (2/c)` one has `c ≤ n` ⟹ `log(n·c) ≤ 2·log n`
and `n·c ≥ 2` ⟹ `log(n·c) > 0`, so each term dominates `½·1/(n·log n)`, whose
divergence is the verified `not_summable_one_div_nat_mul_log`. 0-sorry, 0-axiom,
no new API — mirrors two verified siblings in the same file. Docker build infra
down all session (containerd meta.db I/O error; `docker images` fails), so
shipped UNVERIFIED with full hand-audit of every tactic step against the sibling
proofs it mirrors. The main-file open crux `required_bound_implies_conjecture`
is untouched.

## Current Focus (prior attempts)

None. Attempt 5 (2026-07-07) was a notes-only reconciliation: a full re-read
confirmed `Proofs/Erdos3Problem.lean` (773 lines) is **0-axiom, 1-sorry** and
that every honest, tractable result around the sorry is already formalized. The
knowledge.md File-inventory and axiom count were stale (claimed "1 axiom, 440
lines"; the Euler axiom was discharged in #34559 and the file has since grown);
both corrected. See knowledge.md ADDENDUM (attempt 5). The sole remaining sorry
(`required_bound_implies_conjecture`, weak `o(N/log N)` threshold) is as hard as
Erdős #3 itself — do NOT attack or fake it. This slug is a mature phantom;
future claimants should release without fabricating value.

## Result this iteration (attempt 4)

Four axiom-free, `sorry`-free lemmas added (build: 7743 jobs, verified) — the
**unconditional low-length regime** `k ≤ 2`:

1. **`infinite_of_hasDivergentSum`** — `HasDivergentSum A → A.Infinite`
   (contrapositive: a finite set has a `Fintype`-summable reciprocal sum via
   `hasSum_fintype`). This is the *hypothesis-side* companion explicitly promised
   in the `infinite_of_containsArbitrarilyLongAP` docstring but previously absent.
2. **`containsAP_two_of_lt`** — `a,b ∈ A`, `a < b` ⟹ `ContainsAP A 2`
   (`{a,b} = ArithProg a (b-a) 2`, common difference `b-a > 0`).
3. **`containsAP_two_of_infinite`** — an infinite `A ⊆ ℕ` has two distinct
   elements (`h.diff (finite_singleton a)` nonempty), hence a genuine 2-AP.
4. **`hasDivergentSum_containsAP_le_two`** — the payoff: `HasDivergentSum A →
   ∀ k ≤ 2, ContainsAP A k` (via `containsAP_of_le`). This is Erdős #3 proved
   *verbatim and unconditionally* on the low-length regime — no Roth bound. The
   entire open content of the conjecture lives at `k ≥ 3`, matching the Roth
   floor `k-1` (`rothNumber_ge_min`): below length 3 there is no arithmetic
   content on either side of the implication.

## Result attempt 3

Two axiom-free, `sorry`-free lemmas added (build: 7743 jobs, verified):

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

Leave the threshold-critical sorry documented. The elementary bracketing is now
complete on both axes: Roth number (`rothNumber_ge_min`/`_le_window`) and AP
length (`hasDivergentSum_containsAP_le_two` for `k ≤ 2`). Only remaining shallow
follow-up: expose `summable_of_strongBound` as a reusable density→convergence
lemma elsewhere. The environment recipe (external `/tmp` worktree — the managed
`.loom/worktrees/researcher-5` was hard-reset AND deleted mid-session by the
daemon; commit in `/tmp` immediately —
`LEAN_MEMORY_LIMIT=16384 LEAN_SKIP_CACHE=true`) is proven to work for this file.

## Attempts

- 1: threshold analysis + StrongBound design (verification deferred — no build).
- 2: repaired non-compiling file; compiled & verified the StrongBound reduction
  (0-axiom, 7743 jobs); memory bump to 16 GB needed (transient SIGBUS at 8 GB).
- 3: added `isAPFree_of_card_lt` + `rothNumber_ge_min` (trivial Roth lower
  bound, brackets `rothNumber_le_window`); 0-axiom, 0-sorry, 7743 jobs verified.
- 4: added the low-length regime `k ≤ 2` (`infinite_of_hasDivergentSum`,
  `containsAP_two_of_lt`, `containsAP_two_of_infinite`,
  `hasDivergentSum_containsAP_le_two`); 0-axiom, 0-sorry, 7743 jobs verified.
- 5: **VERIFIED** the previously build-blocked Bertrand-series divergence.
  Recovered `Proofs/Erdos3LogHarmonic.lean` (staged UNVERIFIED in commit
  fcc4a776011 when the build host was OOM-killing at 32 GB) onto clean main and
  machine-checked it with `docker-build.sh Proofs.Erdos3LogHarmonic` (7743 jobs,
  6.7 s target build). `not_summable_one_div_nat_mul_log`: ∑ 1/(n·log n) diverges
  via Cauchy condensation (`summable_condensed_iff_of_nonneg`) → constant multiple
  of the harmonic series (`not_summable_one_div_natCast`). `#print axioms` reports
  only `[propext, Classical.choice, Quot.sound]` — no `sorryAx`/`ofReduceBool`.
  This substantiates the o(N/log N) counterexample profile in the
  `StrongRequiredBound` docstring. Build host was healthy this session (0 docker
  lean-build containers at build time), unlike the OOM-blocked session that staged it.
  The threshold-critical `required_bound_implies_conjecture` sorry remains
  documented and untouched (as hard as Erdős #3 itself).
