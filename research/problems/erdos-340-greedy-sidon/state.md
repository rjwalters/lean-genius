# Current State

**Phase**: PARTIAL (verified sub-results; headline conjecture remains OPEN)
**Since**: 2026-06-16
**Iteration**: 3

## Current Focus

The three `greedySidonSeq*` existence axioms in `Erdos340GreedySidon.lean` are fully
*dischargeable* — an explicit greedy (Mian–Chowla) construction proves them. The discharge
is drafted and verified-by-inspection (PR #25131, unregistered orphan
`Erdos340GreedyConstructionDischarge.lean`); the only remaining step is the **inline** that
actually drops the registered axiom count, which is blocked on the Docker build wrapper.

## Active Approach

New companion file `Proofs/Erdos340GreedyExtension.lean` (0 sorries, 0 axioms):

- `sidon_insert_of_large` — adding a top element `m > sup(A)` to a Sidon set keeps it
  Sidon unless a forbidden collision `m + a = c + d` (a,c,d ∈ A) occurs.
- `sidon_exists_extension` — every finite Sidon set extends, above any bound `B`, to a
  strictly larger Sidon set. Key estimate: any `m > 2·sup(A)` works, because a collision
  forces `m = c + d − a ≤ 2·sup(A)`. No finiteness-counting of the forbidden set needed.
- `sidon_extension_points_infinite` — the set of valid extension points is infinite.

This is the verified content justifying the existence axiom `greedySidonSeq`: the greedy
construction never gets stuck.

Also fixed: two dangling `/--` doc-comments in `Erdos340GreedySidon.lean` (lines 428, 455)
that had no attached declaration, introduced by #24965. They caused
`unexpected token '/--'; expected 'lemma'` and broke compilation of the whole `Proofs`
library. Converted to `/-` block comments.

## Blockers

The headline growth bound `|A ∩ [1,N]| ≫ N^{1/2−ε}` (Erdős #340) is an OPEN conjecture
and is not attempted. The best known bound is `N^{1/3}`.

## Discharge status (verified by inspection, 2026-06-16 iter 3)

The greedy construction discharging the three `greedySidonSeq*` axioms exists and is
correct on inspection. It reuses the already-merged, verified extension lemmas
(`sidon_exists_extension`, `sidon_insert_of_large`, #25087). The construction:

- `instDecidableIsSidon` — `Decidable (IsSidon A)` via `decidable_of_iff` over the bounded
  4-binder form. Binder order matches `IsSidon` (def line 76: `a b c d`, then `∈`, then
  `≤`, then sum-eq), so the forward map is `fun h a b c d ha hb hc hd => h a ha b hb …`.
- `nextSidon S b` — `if h : ∃ m, b < m ∧ IsSidon (insert m S) then Nat.find h else b+1`;
  `nextSidon_spec` discharges the `∃` from `sidon_exists_extension`, so it never hits junk.
- `greedyPair : ℕ → ℕ × Finset ℕ` (a₀=1, {1}), `greedySeq n = (greedyPair n).1`,
  `greedySeqSet n = (greedyPair n).2`.
- `greedySeqSet_isSidon` (induction; base `isSidon_singleton 1`), `greedySeq_lt_succ`,
  `greedySeq_strictMono` (`strictMono_nat_of_lt_succ`),
  `greedySeqSet_eq_image` (induction; `range_succ` + `image_insert`).

## Next Action — one-shot inline when Docker is back up

This is the only step left to take registered `axiomCount` from **4 → 1** (the remaining
axiom being `sidon_upper_bound`, the Erdős–Turán √N upper bound — a genuinely separate
known result, not the open conjecture). Recipe:

1. **Resolve the import cycle.** The construction needs `sidon_exists_extension`, which
   currently lives in `Erdos340GreedyExtension.lean` — a file that *imports* the base
   `Erdos340GreedySidon.lean`. So move `sidon_insert_of_large` + `sidon_exists_extension`
   *into* the base file, placed before "Part 3" (they only need `IsSidon` / `isSidon_singleton`,
   both defined earlier at lines 76/90, and `open Finset`, already in scope). Leave
   `sidon_extension_points_infinite` in the Extension file — it still resolves via the
   base import. Remove the two moved lemmas from the Extension file to avoid duplicates.
2. **Replace the axioms** (base file lines 396–403) with the construction above, then set
   `noncomputable def greedySidonSeq : ℕ → ℕ := greedySeq`, and turn
   `greedySidonSeq_strictMono` / `greedySidonSeq_isSidon` into theorems
   (`:= greedySeq_strictMono`; for `isSidon` use `greedySeqSet_eq_image` ▸ `greedySeqSet_isSidon`).
   `Erdos340Problem.lean` has its **own** independent `greedySidon`, so it is unaffected.
3. `./proofs/scripts/docker-build.sh Proofs.Erdos340GreedySidon` (then the Extension target).
   Docker exits 0 even on Lean errors — `grep error:` the log.
4. Update `src/data/proofs/erdos-340-greedy-sidon-oq-01/meta.json` `axiomCount` 4 → 1.

The full drafted file is on PR #25131's branch; copy its body (minus the orphan header) and
the import becomes unnecessary once the extension lemmas are co-located.

**Do NOT** apply this edit while the Docker wrapper is down: an unverified change to a
registered file reaches `main` through gateless math merges and would break the whole
`Proofs` build. The 2026-06-16 sessions (R2 #25131, R12 branch, R9 #25087, R8 iter 4) were
all blocked here by the same Docker stall, not by any mathematical gap.

## Iteration 4 (2026-06-16, researcher-8)

Re-confirmed the blocker. The merged orphan `Erdos340GreedyConstructionDischarge.lean`
(PR #25131) and the extension lemmas (`Erdos340GreedyExtension.lean`, #25087) are both on
`main`, so the inline recipe above is fully ready — no remaining mathematical work, only the
Docker-verified inline + `meta.json` axiomCount 4 → 1. This session Docker was **unusably
contended**: `docker info` reported "UP" but `docker ps` *hung past a 15 s timeout* (host
load ~26, ~18 concurrent `docker-build.sh` peers). A build cannot complete and, per the
warning above, an unverified registered-file edit must not be pushed. No new PR — the work
is staged; next session with a free Docker should execute the 4-step recipe verbatim.

Recommendation: this slot has now been Docker-blocked across 4+ sessions with zero
mathematical gap remaining. Consider flagging **BLOCKED-on-infra** so claim-random stops
serving it until Docker capacity frees up.

## Attempt Counts

- Total attempts: 3
- Current approach attempts: 3
- Approaches tried: 1
