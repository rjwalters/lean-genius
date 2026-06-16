# Current State

**Phase**: PARTIAL (verified sub-results; headline conjecture remains OPEN)
**Since**: 2026-06-16
**Iteration**: 3

## Current Focus

Discharging the *well-definedness* content behind the greedy-construction axioms in
`Erdos340GreedySidon.lean`, and repairing a parse error in that file.

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

## Iteration 3 (2026-06-16, researcher-2) — greedy construction, discharges 3 axioms (build-pending)

New UNREGISTERED orphan companion `Proofs/Erdos340GreedyConstructionDischarge.lean`
constructs the greedy (Mian–Chowla) sequence explicitly and proves it discharges the three
`greedySidonSeq*` existence axioms in `Erdos340GreedySidon.lean`:

- `instDecidableIsSidon` — `Decidable (IsSidon A)` via `decidable_of_iff` against the
  binder-reordered bounded form (Finset four-fold `∀ … ∈ A`).
- `nextSidon S b` — smallest `m > b` keeping the set Sidon (`open Classical`; junk `b+1`
  if none). `nextSidon_spec` discharges well-definedness using the already-verified
  `sidon_exists_extension` (so the greedy rule never gets stuck).
- `greedyPair`/`greedySeq`/`greedySeqSet` — structural recursion from `a₀ = 1`.
- `greedySeqSet_isSidon`, `greedySeq_strictMono`, `greedySeqSet_eq_image`.
- `greedySidonSeq_strictMono_discharge`, `greedySidonSeq_isSidon_discharge` — exactly the
  two axiom statements, now theorems (under `greedySidonSeq := greedySeq`).

**Status: BUILD-PENDING.** Docker daemon unresponsive this session (`docker info`/`docker ps`
time out, rc=124; host load ≈27). The file is an unregistered orphan (not in `Proofs.lean`)
so it carries zero gallery-build risk even unverified. `meta.json` axiomCount intentionally
LEFT unchanged — the axioms still live in the registered file until a verified inline. This
deliberately avoids the registered-file edit approach of branch
`research/erdos-340-greedy-construction` (which would gateless-break the whole `Proofs`
build if it failed to compile, since math PRs merge with no Lean gate).

**Next session (Docker up):** `./proofs/scripts/docker-build.sh
Proofs.Erdos340GreedyConstructionDischarge`, grep log for `error:` (wrapper exits 0 on Lean
error). Risk spots: `instDecidableIsSidon` synthesis → fallback `decidable_of_iff' _ (by
simp [IsSidon])`; `unfold nextSidon; exact dif_pos hex` → fallback `simp only [nextSidon,
dif_pos hex]`; `hrec := rfl` in `greedySeqSet_eq_image` (structural Nat rec, should hold)
→ fallback `simp only [greedySeqSet, greedyPair]`. If green, inline into
`Erdos340GreedySidon.lean` replacing the 3 axioms (set `def greedySidonSeq := greedySeq`),
drop axiomCount 4→1, update meta.

## Next Action

Verify the orphan with Docker when the daemon recovers, then inline to discharge the 3
axioms. Headline `N^{1/2−ε}` growth bound remains OPEN (untouched).

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1
